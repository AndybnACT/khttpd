#define pr_fmt(fmt) KBUILD_MODNAME ": " fmt
// #define DEBUG

#include "http_server.h"
#include "abn.h"

#include <linux/kthread.h>
#include <linux/sched/signal.h>
#include <linux/tcp.h>
#include <linux/types.h>
#include <linux/workqueue.h>

#include "http_parser.h"

#define CRLF "\r\n"

#define HTTP_RESPONSE_200_DUMMY                                \
    ""                                                         \
    "HTTP/1.1 200 OK" CRLF "Server: " KBUILD_MODNAME CRLF      \
    "Content-Type: text/plain" CRLF "Content-Length: %ld" CRLF \
    "Connection: Close" CRLF CRLF "%s" CRLF
#define HTTP_RESPONSE_200_KEEPALIVE_DUMMY                      \
    ""                                                         \
    "HTTP/1.1 200 OK" CRLF "Server: " KBUILD_MODNAME CRLF      \
    "Content-Type: text/plain" CRLF "Content-Length: %ld" CRLF \
    "Connection: Keep-Alive" CRLF CRLF "%s" CRLF
#define HTTP_RESPONSE_501                                              \
    ""                                                                 \
    "HTTP/1.1 501 Not Implemented" CRLF "Server: " KBUILD_MODNAME CRLF \
    "Content-Type: text/plain" CRLF "Content-Length: 21" CRLF          \
    "Connection: Close" CRLF CRLF "501 Not Implemented" CRLF
#define HTTP_RESPONSE_501_KEEPALIVE                                    \
    ""                                                                 \
    "HTTP/1.1 501 Not Implemented" CRLF "Server: " KBUILD_MODNAME CRLF \
    "Content-Type: text/plain" CRLF "Content-Length: 21" CRLF          \
    "Connection: KeepAlive" CRLF CRLF "501 Not Implemented" CRLF

#define RECV_BUFFER_SIZE 4096

struct http_request {
    struct socket *socket;
    enum http_method method;
    char request_url[128];
    int complete;
};

static int http_server_recv(struct socket *sock, char *buf, size_t size)
{
    struct kvec iov = {.iov_base = (void *) buf, .iov_len = size};
    struct msghdr msg = {.msg_name = 0,
                         .msg_namelen = 0,
                         .msg_control = NULL,
                         .msg_controllen = 0,
                         .msg_flags = 0};
    return kernel_recvmsg(sock, &msg, &iov, 1, size, msg.msg_flags);
}

static int http_server_send(struct socket *sock, const char *buf, size_t size)
{
    struct msghdr msg = {.msg_name = NULL,
                         .msg_namelen = 0,
                         .msg_control = NULL,
                         .msg_controllen = 0,
                         .msg_flags = 0};
    int done = 0;
    while (done < size) {
        struct kvec iov = {
            .iov_base = (void *) ((char *) buf + done),
            .iov_len = size - done,
        };
        int length = kernel_sendmsg(sock, &msg, &iov, 1, iov.iov_len);
        if (length < 0) {
            pr_err("write error: %d\n", length);
            break;
        }
        done += length;
    }
    return done;
}

static unsigned long count_digit(unsigned long num)
{
    unsigned long cnt;
    for (cnt = 0; num != 0; cnt++)
        num /= 10;
    return cnt;
}


static bn bn_fib_doubling(uint64_t k)
{
    bn a, b;
    bn t1, t2, bb, tmp, bsquare, asquare;
    int clz;
    int f_i = 0;

    bn_init(&a);
    bn_init(&b);
    bn_init(&t1);
    bn_init(&t2);
    bn_init(&bb);
    bn_init(&tmp);
    bn_init(&bsquare);
    bn_init(&asquare);

    bn_set(&a, 0);
    bn_set(&b, 1);
    if (k <= 1) {
        return k == 0 ? a : b;
    }

    clz = __builtin_clzll(k);
    for (int i = (64 - clz); i > 0; i--) {
        bn_assign(&bb, &b);
        __bn_shld(&bb, 1);
        bn_sub(&tmp, &bb, &a);
        bn_mul_comba(&t1, &a, &tmp);
        bn_mul_comba(&asquare, &a, &a);  // comba square is ready on my mac
        bn_mul_comba(&bsquare, &b, &b);  // comba square is ready
        bn_add(&t2, &asquare, &bsquare);

        bn_assign(&a, &t1);
        bn_assign(&b, &t2);
        if (k & (1ull << (i - 1))) {  // current bit == 1
            bn_add(&t1, &a, &b);
            bn_assign(&a, &b);
            bn_assign(&b, &t1);
            f_i = (f_i * 2) + 1;
        } else {
            f_i = f_i * 2;
        }
    }

    bn_free(&b);
    bn_free(&t1);
    bn_free(&t2);
    bn_free(&bb);
    bn_free(&tmp);
    bn_free(&bsquare);
    bn_free(&asquare);
    return a;
}


static char *abn_calculate_fib(unsigned long k)
{
    char *res;
    unsigned long long *num;
    unsigned long digit = 10;
    bn a;
    pr_info("k = %ld\n", k);

    bn_init(&a);
    a = bn_fib_doubling(k);
    digit = a.cnt * 16 + 2 + 1;  // 2 for "0x"
    // bn_print(&a);
    num = bn_getnum(&a);
    pr_info("number of digit: %ld\n", digit);

    res = (char *) kmalloc(digit + 1, GFP_KERNEL);
    if (!res)
        return NULL;
    snprintf(res, 19, "0x%016llx", num[a.cnt - 1]);
    for (int i = a.cnt - 2, j = 18; i >= 0; i--, j += 16)
        snprintf(res + j, 17, "%016llx", num[i]);

    bn_free(&a);
    return res;
}

static int http_server_response(struct http_request *request, int keep_alive)
{
    char *response;
    char *res_buf;
    char *res;
    int rc;
    unsigned long clen;
    unsigned long k = 0;
    unsigned long size = 0;

    pr_info("requested_url = %s\n", request->request_url);
    if (request->method != HTTP_GET)
        response = keep_alive ? HTTP_RESPONSE_501_KEEPALIVE : HTTP_RESPONSE_501;
    else
        response = keep_alive ? HTTP_RESPONSE_200_KEEPALIVE_DUMMY
                              : HTTP_RESPONSE_200_DUMMY;
    size += strlen(response);

    if (strncmp(request->request_url, "/fib/", 5) == 0 &&
        request->request_url[5] != '-') {
        rc = kstrtol(request->request_url + 5, 10, &k);
        if (rc) {
            pr_err("cannot convert number in url\n");
            k = 0;
        }
        res = abn_calculate_fib(k);
        if (!res) {
            pr_err("cannot allocate space for result buffer\n");
            goto err;
        }
    } else {
        res = kmalloc(12, GFP_KERNEL);
        if (!res) {
            pr_err("cannot allocate space for result buffer\n");
            goto err;
        }
        memcpy(res, "Hello-World", 12);
    }
    clen = strlen(res) + 1;  // Content-length
    size += clen;
    size += count_digit(clen);  // length of Content-length

    res_buf = (char *) kmalloc(size, GFP_KERNEL);
    if (!res_buf) {
        pr_err("cannot allocate space for response bufer");
        goto err_free_res;
    }
    snprintf(res_buf, size, response, clen, res);

    http_server_send(request->socket, res_buf, size);
    pr_debug("sending %s\n", res_buf);
    kfree(res_buf);
err_free_res:
    kfree(res);
err:
    return 0;
}

static int http_parser_callback_message_begin(http_parser *parser)
{
    struct http_request *request = parser->data;
    struct socket *socket = request->socket;
    memset(request, 0x00, sizeof(struct http_request));
    request->socket = socket;
    return 0;
}

static int http_parser_callback_request_url(http_parser *parser,
                                            const char *p,
                                            size_t len)
{
    struct http_request *request = parser->data;
    size_t pos;
    for (pos = 0; pos < 128 && request->request_url[pos]; pos++)
        ; /* strlen */
    len = (pos + len >= 128) ? 128 - pos - 1 : len;
    strncat(request->request_url, p, len);
    return 0;
}

static int http_parser_callback_header_field(http_parser *parser,
                                             const char *p,
                                             size_t len)
{
    return 0;
}

static int http_parser_callback_header_value(http_parser *parser,
                                             const char *p,
                                             size_t len)
{
    return 0;
}

static int http_parser_callback_headers_complete(http_parser *parser)
{
    struct http_request *request = parser->data;
    request->method = parser->method;
    return 0;
}

static int http_parser_callback_body(http_parser *parser,
                                     const char *p,
                                     size_t len)
{
    return 0;
}

static int http_parser_callback_message_complete(http_parser *parser)
{
    struct http_request *request = parser->data;
    http_server_response(request, http_should_keep_alive(parser));
    request->complete = 1;
    return 0;
}

struct worker {
    struct socket *socket;
    struct work_struct work;
};

static int http_server_worker(void *arg)
{
    char *buf;
    struct http_parser parser;
    struct worker *worker = (struct worker *) arg;
    struct http_parser_settings setting = {
        .on_message_begin = http_parser_callback_message_begin,
        .on_url = http_parser_callback_request_url,
        .on_header_field = http_parser_callback_header_field,
        .on_header_value = http_parser_callback_header_value,
        .on_headers_complete = http_parser_callback_headers_complete,
        .on_body = http_parser_callback_body,
        .on_message_complete = http_parser_callback_message_complete};
    struct http_request request;
    struct socket *socket;

    socket = worker->socket;

    allow_signal(SIGKILL);
    allow_signal(SIGTERM);

    buf = kmalloc(RECV_BUFFER_SIZE, GFP_KERNEL);
    if (!buf) {
        pr_err("can't allocate memory!\n");
        return -1;
    }
    buf[RECV_BUFFER_SIZE - 1] = '\0';

    request.socket = socket;
    http_parser_init(&parser, HTTP_REQUEST);
    parser.data = &request;
    while (!kthread_should_stop()) {
        int ret = http_server_recv(socket, buf, RECV_BUFFER_SIZE - 1);
        if (ret <= 0) {
            if (ret)
                pr_err("recv error: %d\n", ret);
            break;
        }
        http_parser_execute(&parser, &setting, buf, ret);
        if (request.complete && !http_should_keep_alive(&parser))
            break;
    }
    kernel_sock_shutdown(socket, SHUT_RDWR);
    sock_release(socket);
    kfree(buf);
    pr_debug("worker %d is leaving\n", current->pid);
    kfree(worker);
    return 0;
}

void khttp_wq_worker(struct work_struct *w)
{
    struct worker *arg = container_of(w, struct worker, work);
    http_server_worker(arg);
    return;
}

int http_server_daemon(void *arg)
{
    int rc = -ENOMEM;
    struct socket *socket;
    struct worker *worker;
    struct http_server_param *param = (struct http_server_param *) arg;

    allow_signal(SIGKILL);
    allow_signal(SIGTERM);
    param->wq = alloc_workqueue("khttp-wq", WQ_UNBOUND | WQ_SYSFS, 0);
    if (!param->wq) {
        pr_err("cannot allocate workqueue\n");
        goto out;
    }

    while (!kthread_should_stop()) {
        int err = kernel_accept(param->listen_socket, &socket, 0);
        if (err < 0) {
            if (signal_pending(current))
                break;
            pr_err("kernel_accept() error: %d\n", err);
            continue;
        }
        worker = kmalloc(sizeof(struct worker), GFP_KERNEL);
        if (!worker) {
            pr_err("can't create more worker metadata\n");
            goto out_freewq;
        }
        /* queue work */
        INIT_WORK(&worker->work, khttp_wq_worker);
        worker->socket = socket;
        if (!queue_work(param->wq, &worker->work))
            pr_err("ERROR, cannot queue (worker is not freeed!!)\n");
    }
    destroy_workqueue(param->wq);
    return 0;
out_freewq:
    destroy_workqueue(param->wq);
out:
    return rc;
}
