from collections import defaultdict

class FDTree(object):
    def __init__(self, U):
        self.U = U
        self.n_attributes = len(U)
        # self.fds = defaultdict(list)
        self.fds = []#defaultdict(list)
        self.fd_index = [[] for i in range(self.n_attributes)]#defaultdict(list)
        self.counts = []#defaultdict(lambda: 0)
        self.discounts = []
        self.trivial = []
        self.n_fds = 0
        self.recursions = 0

    def add_fd(self, ant, con):
        
        # self.fds[len(ant)].append((set(ant), set(con)))
        self.fds.append((set(ant), set(con)))
        for m in ant:
            self.fd_index[m].append(self.n_fds)
        if not bool(ant):
            self.trivial.append(self.n_fds)
        self.counts.append(len(ant))
        self.discounts.append(0)
        self.n_fds+=1


    def read_and_iterate(self, current_node, base):
        for fd in self.fds:
            yield fd

    def read_fds(self):
        for fd in self.fds:
            yield fd

    def l_close_and_iterate(self, current_node, ant, y):
        
        self.recursions += 1
        for i in current_node[1]:
            if i not in ant:
                yield i
        
        for i in ant:
            if current_node[0][i] and current_node[0][i][2] < y:
                for y in self.l_close_and_iterate(current_node[0][i], ant, y):
                    yield y

    def l_close(self, s):
        '''
        Lin Closure
        '''
        
        new_closure = s.copy()
        for i in self.trivial:
            new_closure |= self.fds[i][1]
        
        update = list(new_closure)

        while update:
            m = update.pop()
            # imps.setdefault(m, [])
            for i in self.fd_index[m]:
                imp = self.fds[i]
                self.discounts[i] += 1
                if self.discounts[i] == self.counts[i]:
                    add = imp[1] - new_closure
                    new_closure |= imp[1]
                    update.extend(add)

        for i in range(self.n_fds):
            self.discounts[i] = 0
        return new_closure

if __name__ == "__main__":
    fds = [(set([1]), set([0, 2])), (set([0]), set([3])), (set([3]), set([4]))]
    fdt = FDTree(range(5))
    for fd in fds:
        fdt.add_fd(fd[0], fd[1])

    for i in fdt.read_fds():
        print (i)

    print (fdt.l_close(set([0,1])))
    