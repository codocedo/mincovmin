from collections import defaultdict

class FDTree(object):
    def __init__(self, U):
        self.U = U
        self.n_attributes = len(U)
        self.root = [[None]*self.n_attributes, set([])]
        self.n_fds = 0

    def add_fd(self, ant, con):
        self.n_fds += 1
        current_node = self.root
        ant = sorted(ant, reverse=True)

        while bool(ant):
            x = ant.pop()
            if current_node[0][x] is None:
                # current_node[0][x] = [[None]*self.n_attributes, [False]*self.n_attributes]
                current_node[0][x] = [[None]*self.n_attributes, set([])]
            current_node = current_node[0][x]
        # print current_node
        for i in con:
            # current_node[1][i] = True
            current_node[1].add(i)# = True

    def read_and_iterate(self, current_node, base):
        if bool(current_node[1]):
            yield (base, current_node[1])
        # if sum(current_node[1]):
        #     yield (base, set([i for i, j in enumerate(current_node[1]) if j]))
        # for i, j in filter(lambda (i,j): j == True, enumerate(current_node)):
            
        for i, j in filter(lambda k: type(k[1]) == list, enumerate(current_node[0])):
            for fd in self.read_and_iterate(current_node[0][i], base.union([i])):
                yield fd

    def read_fds(self):
        base = set([])
        for fd in self.read_and_iterate(self.root, base):
            yield fd

    def l_close_and_iterate(self, current_node, ant):
        for i in current_node[1]:#.difference(ant):
            if i not in ant:
                yield i
        for i in ant:
            if current_node[0][i] is not None:
                for y in self.l_close_and_iterate(current_node[0][i], ant):
                    yield y
            

        # if sum(current_node[1]):
        #     for m in set([i for i, j in enumerate(current_node[1]) if j]):
        #         if m not in ant:
        #             yield m

        # for i, j in enumerate(current_node[0]):
        #     # print '\t', i, j
        #     if j is None:
        #         pass
        #     elif type(j) == list and i in ant:
        #         for y in self.l_close_and_iterate(current_node[0][i], ant):
        #             yield y

    def l_close(self, ant):
        closed_ant = set(ant)
        while True:
            # print '\t::',closed_ant
            result = set([])
            for m in self.l_close_and_iterate(self.root, closed_ant):
                # print '\t\t::', m
                result.add(m)
            if bool(result):
                closed_ant.update(result)
            else:
                break
        return closed_ant

if __name__ == "__main__":
    fds = [(set([1]), set([0, 2])), (set([0]), set([3])), (set([3]), set([4]))]
    fdt = FDTree(range(5))
    for fd in fds:
        fdt.add_fd(fd[0], fd[1])

    for i in fdt.read_fds():
        print (i)

    print (fdt.l_close(set([0,1])))