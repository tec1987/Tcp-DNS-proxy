#!/usr/bin/env python
# -*- coding: utf-8 -*-
# cody by zhouzhenster@gmail.com

#
# Change log:
#
# 2011-10-23  use SocketServer to run a multithread udp server
# 2012-04-16  add more public dns servers support tcp dns query
# 2013-05-14  merge code from @linkerlin, add gevent support
# 2013-06-24  add lru cache support
# 2013-08-14  add option to disable cache
# 2014-01-04  add option "servers", "timeout" @jinxingxing
# 2014-04-04  support daemon process on unix like platform
# 2014-05-27  support udp dns server on non-standard port
# 2014-07-08  use json config file
# 2014-07-09  support private host
# 2015-01-14  support dns server auto switch

#  8.8.8.8        google
#  8.8.4.4        google
#  156.154.70.1   Dnsadvantage
#  156.154.71.1   Dnsadvantage
#  208.67.222.222 OpenDNS
#  208.67.220.220 OpenDNS
#  198.153.192.1  Norton
#  198.153.194.1  Norton

import gevent
import os
import socket
import struct
import SocketServer
import argparse
import json
import time
from fnmatch import fnmatch
import logging
import third_party
from pylru import lrucache
import ctypes
import sys
import random

cfg = {}
LRUCACHE = None
DNS_SERVERS = None
FAST_SERVERS = None
SPEED = {}
DATA = {'err_counter': 0, 'speed_test': False}
UDPMODE = False
PIDFILE = '/tmp/tcpdns.pid'
len_AddRRs = 0

def cfg_logging(dbg_level):
    """ logging format
    """
    logging.basicConfig(format='[%(asctime)s][%(levelname)s] %(message)s',
                        level=dbg_level)

def hexdump(src, width=16):
    """ hexdump, default width 16
    """
    FILTER = ''.join(
        [(x < 0x7f and x > 0x1f) and chr(x) or '.' for x in range(256)])
    result = []
    for i in xrange(0, len(src), width):
        s = src[i:i + width]
        hexa = ' '.join(["%02X" % ord(x) for x in s])
        printable = s.translate(FILTER)
        result.append("%04X   %s   %s\n" % (i, hexa, printable))
    return ''.join(result)


def bytetodomain(s):
    """bytetodomain

    03www06google02cn00 => www.google.cn
    """
    qnl = []
    domain = ''
    i = 0
    length = struct.unpack('!B', s[0:1])[0]

    while length != 0:
        i += 1
        qnl.append(s[i-1:i + length])
        domain += s[i:i + length]
        i += length
        length = struct.unpack('!B', s[i:i + 1])[0]
        if length != 0: # 可取消判断，带根域“.”
            domain += '.'

    return (domain, qnl)

def dnsping(ip, port):
    buff =  "\x00\x16\xb2\xc3\x01\x00\x00\x01"
    buff += "\x00\x00\x00\x00\x00\x00\x01\x67"  # '\x67' == 'g'
    buff += "\x02\x63\x6e\x00\x00\x01\x00\x01"  # '\x63\x6e' == 'cn'

    cost = 100
    begin = time.time()
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.settimeout(cfg['socket_timeout'])
        s.connect((ip, int(port)))
        s.send(buff)
        s.recv(2048)
    except Exception as e:
        logging.error('%s:%s, %s' % (ip, port, str(e)))
    else:
        cost = time.time() - begin

    key = '%s:%d' % (ip, int(port))
    if key not in SPEED:
        SPEED[key] = []

    SPEED[key].append(cost)

def TestSpeed():
    global DNS_SERVERS
    global FAST_SERVERS
    global DATA

    DATA['speed_test'] = True

    if cfg['udp_mode']:
        servers = cfg['udp_dns_server']
    else:
        servers = cfg['tcp_dns_server']

    logging.info('Testing dns server speed ...')
    jobs = []
    for i in xrange(0, 6):
        for s in servers:
            ip, port = s.split(':')
            jobs.append(gevent.spawn(dnsping, ip, port))

    gevent.joinall(jobs)

    cost = {}
    for k, v in SPEED.items():
        cost[k] = sum(v)

    d = sorted(cost, key=cost.get)
    FAST_SERVERS = d[:3]
    DNS_SERVERS = FAST_SERVERS

    DATA['err_counter'] = 0
    DATA['speed_test'] = False


def QueryDNS(server, port, qdata):  # 处理传入的UDP包，转发给上游DNS
    """tcp dns request

    Args:
        server: remote tcp dns server
        port: remote tcp dns port
        qdata - querydata: udp dns request packet data

    Returns:
        tcp dns response data
    """

    global DATA, len_AddRRs

    if DATA['err_counter'] >= 10 and not DATA['speed_test']:
        TestSpeed()

    # logging.debug(qdata)
    q_name, qnl = bytetodomain(qdata[12:])
    lqn = len(q_name)
    q_type = struct.unpack('!H', qdata[14+lqn:16+lqn])[0]
    logging.debug('domain:%s, qtype:%x' % (q_name, q_type))
    # logging.debug(qnl)

    # question
    # queries = qdata[12:12+lqn+2+4]  # queries_len = lqn+2+4

    # add DNS compression pointer mutation

    qll = len(qnl)
    AdditionalRRs = qdata[10:12]
    if qll > 1:        # 域名不少于一级 不处理根域和顶级域名(not root or gTLD)
        if AdditionalRRs != '\x00\x00': AddRRs = qdata[18+lqn:]         # 判断是否含有附加部分，并提取
        else:
            AddRRs = '\x00\x00\x29\x10\x00\x00\x00\x00\x00\x00\x00'     # 否则自定义附加部分 0000291000000000000000 len=11(0x0b)
            AdditionalRRs = '\x00\x01'
        len_AddRRs = len(AddRRs)    # 计算附加部分的长度    # len(qdata) - lqn - 18

        qdi = '\x00\x01'            # 查询数 默认 1查询
        cpl = ['\xC0\x04', '\xC0\x06', '\xC0\x08', '\xC0\x0a']	# 结束指针 列表
        rf = random.randint(0,4)	# rf =1|2 时 使用 1查询 并过滤伪包 可用其他国外DNS	其它值为多查询 目前已知仅8888和8844支持
        if rf < 2:	# rn后移 随机重组 1查询 或 n查询
            # [1d25 0100 0001 000000000001 C0C0 00010001 0000291000000000000000 06676f6f676c65 C0C2 03777777 C0C1 03636f6d C004]	1查询	起始指针，rn后移并打乱，返回1个伪包
            # [1d25 0100 0001 000000000001 C0C0 00010001 06676f6f676c65 C0C2 00010001 03777777 C0C1 00010001 03636f6d C004 00010001 0000291000000000000000]	n查询
            # 随机重组被分隔的域名
            lp = [''] * (qll + 1)		# rn的指针数据
            li = range(qll)
            random.shuffle(li)	# li=[3, 0, 2, 1]
            cpl += ['\xC0\x0e', '\xC0\x10']
            qdn = ['\xC0\x30', qdata[lqn + 14: lqn + 18]]	# 查询数据部分
            idx = 0x12	# 当前相对偏移 12+2+4=18
            idc = [0] * (qll + 1)	# qdn列表中 '\xC0\x??'指针的索引

            if rf:		# 1查询 rn后移	随机排序
                idx += len_AddRRs
                qdn.append(AddRRs)
            else: qdi = '\x00' + struct.pack('!B', qll + 1)
                
            # 方法1，使用列表索引
            for i,v in enumerate(li):	# li=[3, 0, 2, 1]	i=0,1,2,3	v=3,0,2,1
                qdn.append(qnl[v])
                lp[v] = '\xC0' + struct.pack('!B', idx)

                if v == qll - 1: lp[v+1] = random.choice(cpl)	# lp[4] = '\xC0\x04'
                qdn.append('\xC0\x3d')	# qdn.append('\xC0' + struct.pack('!B',0x31 + v))	指针占位符 '\xC0\x3d'

                if rf:
                    idc[v+1] = (i+2)*2
                    idx += len(qnl[v]) + 2
                else:
                    idc[v+1] = (i+1)*3
                    qdn.append(struct.pack('!I',random.randint(0,0xFFFFFFFF)))  # '\x00' + '\x01' + '\x00' + '\x01')	# 附加 QTYPE+QCLASS
                    idx += len(qnl[v]) + 6

            for i,v in enumerate(idc): qdn[v] = lp[i]	# 写入指针偏移
            # 结果：
            # qdn = [C030, 00010001, 03636f6d, C004, 00010001, 06676f6f676c65, C032, 00010001, 03777777, C031, 00010001]
            # lp = [0x29, 0x1c, 0x12]
            # qdn = [C029, 00010001, 03636f6d, C004, 00010001, 06676f6f676c65, C012, 00010001, 03777777, C01c, 00010001]

            # qdn = [C030, 00010001, 0000291000000000000000, 03636f6d, C004, 06676f6f676c65, C032, 03777777, C031]
            # lp = [0x2c, 0x23, 0x1d]
            # qdn = [C02c, 00010001, 0000291000000000000000, 03636f6d, C004, 06676f6f676c65, C01d, 03777777, C023]

            ''' 方法2，无列表索引，后面使用 qdn.index 查找索引，逻辑较简单
            for v in li:	# li = [2, 1, 0]
                qdn.append(qnl[v])
                lp[v] = '\xC0' + struct.pack('!B', idx)
                # idx += len(qnl[v])

                if v == qll - 1: qdn.append(random.choice(cpl))	# 判断 并且附加结束指针
                else: qdn.append('\xC0' + struct.pack('!B',0x31 + v))

                if rf: idx += len(qnl[v]) + 2
                else:
                    qdn.append('\x00' + '\x01' + '\x00' + '\x01')
                    idx += len(qnl[v]) + 6

            for i,v in enumerate(lp): qdn[qdn.index('\xC0' + struct.pack('!B',0x30 + i))] = v
            '''

            if not rf: qdn.append(AddRRs)	# 添加 附加数据 可不用判断
            # 结果：
            # qdn = [C029, 00010001, 03636f6d, C004, 00010001, 06676f6f676c65, C012, 00010001, 03777777, C01c, 00010001, 0000291000000000000000]
            # qdn = [C02c, 00010001, 0000291000000000000000, 03636f6d, C004, 06676f6f676c65, C01d, 03777777, C023]

        elif rf > 2:	# r2后移 随机使用2|3个查询
            qdi = '\x00\x03'	# 3查询
            r1 = qnl[-1]	# 顶级域名gTLD
            r2 = qnl[-2]	# 一级域名
            cp_r2 = 0	# r2的偏移指针
            cp_r1 = lqn-len(r2)-len(r1)+19	# 计算 r1的偏移指针 len(rn)-len(r2)-len(r1)+6+12

            qdn = qnl[:-2]	# 提取 r2	前的子域名数据
            qdn.append('\xC0\x00')	# 添加占位字符串 r2的偏移指针 后面还要修改
            qdn.append(qdata[14+lqn:18+lqn])	# 添加QTYPE和QCLASS
            qdn.append(r1)
            cpl += ['\x00', '\x00', '\x00', '\x00']
            cpe = random.choice(cpl)
            qdn.append(cpe)		# 添加 结束指针
            qdn.append(struct.pack('!I',random.randint(0,0xFFFFFFFF)))	# 尾部 QTYPE:A QCLASS:IN 固定值 00010001 不影响查询 '\x00\x01\x00\x01'

            if rf == 4:	# 2查询
                qdn.append(AddRRs)	# 先添加 附加数据
                cp_r2 += len(AddRRs)
                qdi	= '\x00\x02'	# 查询数写为2

            qdn.append(r2)			# 添加 r2
            qdn.append(struct.pack('!2B',0xc0,cp_r1))	# 添加 r1的偏移指针
            
            qdn.append(struct.pack('!I',random.randint(0,0xFFFFFFFF)))	# 多添加一个	QTYPE:A	QCLASS:IN 和 附加数据
            qdn.append(AddRRs)

            ''' # 原始逻辑 2查询后面不会多出 QTYPE:A QCLASS:IN 和 附加数据
            if rf == 4:	# 2查询
                qdn.append(AddRRs)	# 添加 附加数据
                cp_r2 += len(AddRRs)
                qdi	= '\x00\x02'	# 查询数写为2
                qdn.append(r2)		# 添加 r2
                qdn.append(struct.pack('!2B',0xc0,cp_r1))	# 添加 r1的偏移指针
            else:				# 3查询
                qdn.append(r2)		# 添加 r2 (后移为第3个查询)
                qdn.append(struct.pack('!2B',0xc0,cp_r1))	# 添加 r1的偏移指针
                qdn.append('\x00\x01\x00\x01')	# 多添加一个	QTYPE:A	QCLASS:IN
                qdn.append(AddRRs)		# 附加数据
            '''

            cp_r2 += lqn-len(r2)+len(cpe)+23	# 计算 r2的偏移指针 len(rn)-len(r2)+5|6+6+12; 其中 len(rn)=lqn+1 (尾部 结束指针|00 00010001 共5|6字节；指针偏移+QTYPE+QCLASS共6字节；头部12字节)
            qdn[len(qnl[:-2])] = struct.pack('!2B',0xc0,cp_r2)	# 写入 r2的偏移指针
            # 结果：
            # qdn = [03777777, C02a, 00010001, 03636f6d, 00 00010001, 0000291000000000000000, 06676f6f676c65, C016, 00010001, 0000291000000000000000]
            # qdn = [03777777, C01f, 00010001, 03636f6d, 00 00010001, 06676f6f676c65, C016, 00010001, 0000291000000000000000]

        else:	# [0c93 0120 0001 000000000001 03777777 06676f6f676c65 03636f6d c004 00010001 0000291000000000000000]	仅修改结束指针，返回2个伪包
            qdn = [qdata[12:lqn+13], random.choice(cpl), qdata[lqn+14:lqn+18], AddRRs]

        qdl = [qdata[0:4], qdi, qdata[6:10], AdditionalRRs] + qdn	# 添加头部 合成数据

        qdata = ''.join(qdl)	# 修改数据包，生成新的 qdata
    # else: qdn = [qdata[12:lqn+12], random.choice(cpl), qdata[lqn+13:lqn+17], AddRRs]    # 根域和顶级域名 暂不处理
    logging.debug('Send Questions: %s'%' '.join('%02X'%ord(x) for x in qdata))	# repr(qdata).replace('\\x', '')[1:-1]

    # length
    Buflen = struct.pack('!H', len(qdata))
    sendbuf = UDPMODE and qdata or Buflen + qdata

    data = None
    try:
        protocol = UDPMODE and socket.SOCK_DGRAM or socket.SOCK_STREAM
        s = socket.socket(socket.AF_INET, protocol)

        # set socket timeout
        s.settimeout(cfg['socket_timeout'])
        s.connect((server, int(port)))
        s.send(sendbuf)

        # 过滤投毒/污染数据包
        i = 0
        while i < 3:
            data = s.recv(4096)
            if AdditionalRRs == '\x00\x00': break   # 请求包中没有 附加数据
            recv_AddRRs = data[10:12]       # 响应包中附加RR的数量
            if recv_AddRRs == AdditionalRRs: break
            else:
                i += 1
                continue

        logging.debug('Receive Answers: %s'%' '.join('%02X'%ord(x) for x in data))
    except Exception as e:
        DATA['err_counter'] += 1
        logging.error('Server %s: %s' % (server, str(e)))
    finally:
        if s:
            s.close()
        return data     # 返回包有可能是TCP，见配置文件


def private_dns_response(data):
    ret = None

    TID = data[0:2]
    Questions = data[4:6]
    AnswerRRs = data[6:8]
    AuthorityRRs = data[8:10]
    AdditionalRRs = data[10:12]

    q_name, qnl = bytetodomain(data[12:])
    qln = len(q_name)
    # q_type = struct.unpack('!h', data[-4:-2])[0]   # q_type 处理有问题 未考虑查询包含Additional的附加内容，还有其它几处也是如此
    q_type = struct.unpack('!H', data[14+qln:16+qln])[0]

    logging.debug('domain:%s, qtype:%x' % (q_name, q_type))

    try:
        if q_type != 0x0001:
            return

        if Questions != '\x00\x01' or AnswerRRs != '\x00\x00' or AuthorityRRs != '\x00\x00':    #  or AdditionalRRs != '\x00\x00'
            return

        items = cfg['private_host'].items()

        for domain, ip in items:
            if fnmatch(q_name, domain):
                ret = TID
                ret += '\x81\x80'
                ret += '\x00\x01'
                ret += '\x00\x01'
                ret += '\x00\x00'
                ret += '\x00\x00'
                ret += data[12:]
                ret += '\xc0\x0c'
                ret += '\x00\x01'
                ret += '\x00\x01'
                ret += '\x00\x00\xff\xff'
                ret += '\x00\x04'
                ret +=  socket.inet_aton(ip)
    finally:
        return (q_type, q_name, ret)

'''
def check_dns_packet(data, q_type): # 响应包检查    不使用，注释掉
    global UDPMODE

    test_ipv4 = False
    test_ipv6 = False

    if len(data) < 12:
        return False

    Flags = UDPMODE and data[2:4] or data[4:6]

    AddRRs = UDPMODE and data[10:12] or data[12:14]     # 检查并移除附加部分，使用请求包中附加部分的长度，可能会有问题？
    if AddRRs != '\x00\x00':
        if len_AddRRs != 0: data = data[:-len_AddRRs]

    Reply_code = struct.unpack('!H', Flags)[0] & 0x000F

    # TODO: need more check
    if Reply_code == 3: # RCODE（Response code）是由服务端在响应中设置的 4 位响应代码
        return True

        0 – 没有错误。
        1 – 格式错误。服务器无法解释请求。
        2 – 服务器失败。因为服务器的某些故障而不能完成解析请求。
        3 – 名字错误。这个错误代码只会出现在授权的域名服务器的响应中，含义为请求查询的域名不存在。
        4 – 未实现。当前服务器不支持这种查询。
        5 – 拒绝。服务器主动拒绝当前的查询请求。
        6 ~ 15 – 为其他失败保留的代码。

    if q_type == 0x0001:    # A 记录

        # 处理有问题，未考虑附加部分的记录，暂时使用移除附加部分来解决
        ipv4_len = data[-6:-4]
        ipv4_answer_class = data[-12:-10]
        ipv4_answer_type = data[-14:-12]

        test_ipv4 = (ipv4_len == '\x00\x04' and \
                     ipv4_answer_class == '\x00\x01' and \
                     ipv4_answer_type == '\x00\x01')

        if not test_ipv4:

            ipv6_len = data[-18:-16]
            ipv6_answer_class = data[-24:-22]
            ipv6_answer_type =data[-26:-24]

            test_ipv6 = (ipv6_len == '\x00\x10' and \
                         ipv6_answer_class == '\x00\x01' and \
                         ipv6_answer_type == '\x00\x1c')

        if not (test_ipv4 or test_ipv6):
            return False
        

    return Reply_code == 0
'''

def transfer(querydata, addr, server):
    """send udp dns respones back to client program

    Args:
        querydata: udp dns request data
        addr: udp dns client address
        server: udp dns server socket

    Returns:
        None
    """
    global UDPMODE

    if len(querydata) < 12:
        return

    response = None
    t_id = querydata[:2]
    key = querydata[2:].encode('hex')

    q_type, q_domain, response = private_dns_response(querydata)
    if response:
        server.sendto(response, addr)
        return

    UDPMODE = cfg['udp_mode']
    if FAST_SERVERS:
        DNS_SERVERS = FAST_SERVERS
    else:
        DNS_SERVERS = \
                UDPMODE and cfg['udp_dns_server'] or cfg['tcp_dns_server']

    if cfg['internal_dns_server'] and cfg['internal_domain']:
        for item in cfg['internal_domain']:
            if fnmatch(q_domain, item):
                UDPMODE = True
                DNS_SERVERS = cfg['internal_dns_server']

    if LRUCACHE and  key in LRUCACHE:
        response = LRUCACHE[key]
        sendbuf = UDPMODE and response[2:] or response[4:]
        server.sendto(t_id + sendbuf, addr)

        return

    for item in DNS_SERVERS:
        ip, port = item.split(':')

        logging.debug("server: %s port:%s" % (ip, port))
        response = QueryDNS(ip, port, querydata)
        if response is None:    # or not check_dns_packet(response, q_type):  不检查DNS响应包
            continue

        if LRUCACHE is not None:
            LRUCACHE[key] = response

        sendbuf = UDPMODE and response or response[2:]
        server.sendto(sendbuf, addr)

        break

    if response is None:
        logging.error('Tried many times and failed to resolve %s' % q_domain)


def HideCMD():
    whnd = ctypes.windll.kernel32.GetConsoleWindow()
    if whnd != 0:
        ctypes.windll.user32.ShowWindow(whnd, 0)
        ctypes.windll.kernel32.CloseHandle(whnd)



class ThreadedUDPServer(SocketServer.ThreadingMixIn, SocketServer.UDPServer):

    def __init__(self, s, t):
        SocketServer.UDPServer.__init__(self, s, t)


class ThreadedUDPRequestHandler(SocketServer.BaseRequestHandler):
    # Ctrl-C will cleanly kill all spawned threads
    daemon_threads = True
    # much faster rebinding
    allow_reuse_address = True

    def handle(self):
        data = self.request[0]
        socket = self.request[1]
        addr = self.client_address
        transfer(data, addr, socket)    # 只允许传入的UDP查询
'''
import daemon as Daemon
class RunDaemon(Daemon):

    def run(self):
        thread_main(cfg)

def StopDaemon():
    RunDaemon(PIDFILE).stop()
'''
def thread_main(cfg):
    server = ThreadedUDPServer((cfg["host"], cfg["port"]), ThreadedUDPRequestHandler)
    server.serve_forever()
    server.shutdown()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='TCP DNS Proxy')
    parser.add_argument('-f', dest='config_json', type=argparse.FileType('r'),
            required=False, help='Json config file')
    parser.add_argument('-d', dest='dbg_level', action='store_true',
            required=False, default=False, help='Print debug message')
    parser.add_argument('-s', dest="stop_daemon", action='store_true',
            required=False, default=False, help='Stop tcp dns proxy daemon')
    args = parser.parse_args()

    if args.stop_daemon:
        # StopDaemon()
        sys.exit(0)

    if args.dbg_level:
        cfg_logging(logging.DEBUG)
    else:
        cfg_logging(logging.INFO)

    try:
        cfg = json.load(args.config_json)
    except:
        logging.error('Loading json config file error [!!]')
        sys.exit(1)

    if not cfg.has_key("host"):
        cfg["host"] = "0.0.0.0"

    if not cfg.has_key("port"):
        cfg["port"] = 53

    if cfg['udp_mode']:
        DNS_SERVERS = cfg['udp_dns_server']
    else:
        DNS_SERVERS = cfg['tcp_dns_server']

    if cfg['enable_lru_cache']:
        LRUCACHE = lrucache(cfg['lru_cache_size'])

    logging.info('TCP DNS Proxy, https://github.com/henices/Tcp-DNS-proxy')
    logging.info('DNS Servers:\n%s' % DNS_SERVERS)
    logging.info('Query Timeout: %f' % (cfg['socket_timeout']))
    logging.info('Enable Cache: %r' % (cfg['enable_lru_cache']))
    logging.info('Enable Switch: %r' % (cfg['enable_server_switch']))

    if cfg['speed_test']:
        TestSpeed()

    logging.info(
            'Now you can set dns server to %s:%s' % (cfg["host"], cfg["port"]))

    if cfg['daemon_process']:
        if os.name == 'nt':
            HideCMD()
            thread_main(cfg)
        # else:
        #     d = RunDaemon(PIDFILE)
        #     d.start()
    else:
        thread_main(cfg)
