## OPTIMIZATION 1NAIVE VERSION
# USES STRIPED PARTITIONS
# USES A STACK
# USES ORDERED PARTITIONS
# USES A CACHE OF NON FDS

import csv
import sys
import copy
import random
import argparse
import time
from ae_libs.enumerations import LectiveEnum
from ae_libs.boolean_tree import BooleanTree
from ae_libs.fd_tree import FDTree
from ae_libs.fca import FormalContext, next_closure, PreClosure, fast_next_closure
from ae_libs import read_csv
from itertools import product
from collections import defaultdict
from functools import reduce

def mine_fds(ctx, closure):
    U = set(ctx.M)
    fdt = FDTree(U)
    
    A = closure(set([]))

    if bool(A):
        fdt.add_fd(set([]), A)
    i = max(ctx.M)

    while len(A) < len(ctx.M):
        
        for j in reversed(ctx.M):
            if j in A:
                A.remove(j)
            else:
                B = fdt.l_close(A.union([j]))
                if not bool(B-A) or j <= min(B-A):
                    A = B
                    i = j
                    break
        AII = closure(A)
        # print sorted(A), sorted(AII)
        if len(A) < len(AII):
            fdt.add_fd(A, AII-A)
        if not bool(AII-A) or i <= min(AII-A):
            A = AII
            i = max(ctx.M)
        else:
            A = A.intersection(set([i for i in range(i+1)]))
    return fdt

def match(t1, t2):
    return set([i for i, (a,b) in enumerate(zip(tuples[t1], tuples[t2])) if a==b ])

def check(X, XJJ, tuples, n_atts, cache, rand_tuples):
    '''
    Linear check an FD X -> XJJ
    '''
    signatures = {}
    tuple_map = {}
    
    preintent = sorted(X)
    members = sorted(XJJ-X)
    AII = set(range(len(members)))
    
    
    for h in range(len(tuples)):
        ti = rand_tuples[h]
        row = tuples[ti]
        left = tuple([row[att] for att in preintent])
        right = tuple([row[att] for att in members])
        sign = signatures.get(left, None)
        if sign is None:
            signatures[left] = right
            tuple_map[left] = ti
        elif any(sign[idx] != right[idx] for idx in AII):
            i = ti
            j = tuple_map[left]
            new_point = (i,j) if i<j else (j,i)
            # match = [tuples[i][att]==tuples[j][att] for att in range(n_atts) ]
            cache[new_point] = set([att for att in range(n_atts) if tuples[i][att]==tuples[j][att]])

            AII.difference_update(list(filter(lambda att: sign[att] != right[att], AII)))

        if not bool(AII):
            break
    
    AII = X.union([members[idx] for idx in AII])

    return AII

def attribute_exploration_pps(tuples):
    U = range(len(tuples[0])) # Attributes
    n_atts = len(U)
    m_prime = [set([]) for i in range(len(U))]
    g_prime = []
    
    rand_tuples = list(range(len(tuples)))
    rand_tuples.sort(key=lambda i: len(set(tuples[i])))

    fctx = FormalContext(g_prime, m_prime)
    sampled_tuples = []

    representations = [[row[j] for row in tuples] for j in U]

    # ORDERING
    order = [(len(set(r)), ri) for ri, r in enumerate(representations)]
    order.sort(key=lambda k: k[0], reverse=False)
    #print (order)
    order = {j[1]:i for i,j in enumerate(order)} #Original order -> new order
    inv_order = {i:j for j,i in order.items()}
    for ti, t in enumerate(tuples):
        tuples[ti] = [t[inv_order[i]] for i in range(len(t))]
    
    # # END ORDERING
    Mjs = [set() for i in range(n_atts)]
    stack = [[None, None],[None, set([]), Mjs]]

    X = set([])
    
    fdt = FDTree(U)
    m_i = -1
    
    cycles = 0
    cycles2 = 0
    XJ = set([])
    XJJ = fctx.closed_set(X)
    count_good_points = 0
    USet = set(U)
    ncls = 0
    while X != U:
        
        cycles += 1
        if cycles%1000 == 0:
            print ("\rFDs:{}/{}/{}/{}/{} - {: <100}".format(fdt.n_fds, cycles, cycles2, len(g_prime), (sum([len(mp) for mp in m_prime]))/len(m_prime), ','.join(map(str, sorted(X)))), end='') #stack
            sys.stdout.flush()
        
        if m_i >= 0:
            XJ = stack[-2][1].intersection(m_prime[m_i])
            if bool(XJ):
                XJJ = reduce(set.intersection, (g_prime[g] for g in XJ))
                if len(XJ) == 1:
                    XJJ = set(XJJ)
                # SXJ = sorted(XJ, key=lambda g: len(g_prime[g]))
                # XJJ = copy.copy(g_prime[SXJ[0]])
                # for g in SXJ[1:]:
                #     XJJ.intersection_update(g_prime[g])
                #     if len(XJJ) == len(X):
                #         break
            else:
                XJJ = set(range(len(m_prime)))

        cache = {}
        XSS = None
        n_x = len(X)
        
        count_good_points += n_x == len(XJJ)

        while n_x < len(XJJ):
            cycles2 += 1
            # sys.stdout.flush()
            if XSS is None:
                XSS = check(X, XJJ, tuples, n_atts, cache, rand_tuples)
                cache = sorted(cache.items(), key=lambda k: len(k[1]))
                
            # sys.stdout.flush()
            
            if len(XJJ) == len(XSS):
                fdt.add_fd(X, XJJ)
                break
            else:
                
                sampled_tuple, gp = cache.pop()
                
                # for t in sampled_tuple:
                #     dist[t] += 1
                sampled_tuples.append(sampled_tuple)
                XJ.add(len(g_prime))
                for i in stack[1:]:
                    i[1].add(len(g_prime))
                for x in gp:
                    m_prime[x].add(len(g_prime))
                g_prime.append(gp)
                XJJ.intersection_update(gp)
        
        if not bool(XJJ-X) or m_i <= min(XJJ-X):
            m_i = U[-1]
            X = XJJ
        else:
            X.difference_update([m for m in X if m > m_i])

        stack[-1][1] = XJ

        X, m_i,c = fast_next_closure(X, U, fdt.l_close, m_i, stack)

        ncls += c

        stack[-1][0] = m_i

    #for g in g_prime:
    #    print (g)

    L = list(fdt.read_fds())
    print ("\nNUMBER OF FDS:{}".format(len(L)))
    print ("SAMPLING CONTEXT SIZE:{}".format(len(g_prime)))
    print ("CYCLES:",cycles)
    print ("GOOD CLOSURES:", count_good_points)
    print ("Closures:", ncls)
    print(fdt.recursions)


if __name__ == "__main__":
    
    __parser__ = argparse.ArgumentParser(description='FD Miner - Sampling-based Version')
    __parser__.add_argument('database', metavar='database_path', type=str, help='path to the formal database')
    __parser__.add_argument('-s', '--separator', metavar='separator', type=str, help='Cell separator in each row', default=',')
    # __parser__.add_argument('-p', '--use_patterns', help='Use Pattern Structures for DB', action='store_true')
    __parser__.add_argument('-i', '--ignore_headers', help='Ignore Headers', action='store_true')
    args = __parser__.parse_args()

    tuples = read_csv(args.database, separator=args.separator)
    
    t0 = time.time()
    attribute_exploration_pps(tuples)
    print ("TIME: {}s".format(time.time()-t0))

