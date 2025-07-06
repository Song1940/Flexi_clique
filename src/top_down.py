import networkx as nx
import sys, math
from collections import defaultdict
from collections import deque
import time
import argparse
import heapq
import os


sys.setrecursionlimit(10 ** 6)



class Node:
    __slots__ = ['id', 'left', 'right', 'parent', 'rev']

    def __init__(self, id):
        self.id = id
        self.left = None
        self.right = None
        self.parent = None
        self.rev = False

def is_root(x):
    return (x.parent is None) or (x.parent.left != x and x.parent.right != x)


def push(x):
    if x and x.rev:
        x.left, x.right = x.right, x.left
        if x.left:
            x.left.rev ^= True
        if x.right:
            x.right.rev ^= True
        x.rev = False


def update(x):
    pass


def rotate(x):
    p = x.parent
    g = p.parent
    push(p)
    push(x)
    if p.left == x:
        p.left = x.right
        if x.right:
            x.right.parent = p
        x.right = p
    else:
        p.right = x.left
        if x.left:
            x.left.parent = p
        x.left = p
    p.parent = x
    x.parent = g
    if g:
        if g.left == p:
            g.left = x
        elif g.right == p:
            g.right = x
    update(p)
    update(x)


def splay(x):
    while not is_root(x):
        p = x.parent
        g = p.parent
        if not is_root(p):
            if (g.left == p) == (p.left == x):
                rotate(p)  # zig-zig
            else:
                rotate(x)  # zig-zag
        rotate(x)
    push(x)
    update(x)


def access(x):
    last = None
    y = x
    while y:
        splay(y)
        y.right = last
        update(y)
        last = y
        y = y.parent
    splay(x)
    return last


def make_root(x):
    access(x)
    x.rev ^= True
    push(x)


def find_root(x):
    access(x)
    while x.left:
        push(x)
        x = x.left
    splay(x)
    return x


def connected_lct(x, y):
    return find_root(x) == find_root(y)


def link_lct(x, y):
    make_root(x)
    if find_root(y) != x:
        x.parent = y


def cut_lct(x, y):
    make_root(x)
    access(y)
    if y.left == x:
        y.left.parent = None
        y.left = None
    update(y)


class LinkCutTree:
    def __init__(self, n):
        self.n = n
        self.nodes = [Node(i) for i in range(n)]

    def connected(self, u, v):
        return connected_lct(self.nodes[u], self.nodes[v])

    def link(self, u, v):
        if not self.connected(u, v):
            link_lct(self.nodes[u], self.nodes[v])

    def cut(self, u, v):
        # 양 방향 모두 시도 (어느 쪽이 부모인지 모를 수 있으므로)
        make_root(self.nodes[u])
        access(self.nodes[v])
        if self.nodes[v].left == self.nodes[u]:
            self.nodes[v].left.parent = None
            self.nodes[v].left = None
            update(self.nodes[v])
        else:
            make_root(self.nodes[v])
            access(self.nodes[u])
            if self.nodes[u].left == self.nodes[v]:
                self.nodes[u].left.parent = None
                self.nodes[u].left = None
                update(self.nodes[u])



class FullyDynamicConnectivity:
    def __init__(self, n):
        self.n = n
        self.comp_count = n
        self.L = math.ceil(math.log2(n)) if n > 1 else 1  # 최대 레벨
        self.forests = [LinkCutTree(n) for _ in range(self.L + 1)]
        self.non_tree_edges = [set() for _ in range(self.L + 1)]
        self.edge_level = {}
        self.is_tree_edge = {}

    def insert_edge(self, u, v):
        if u > v:
            u, v = v, u
        if (u, v) in self.edge_level:
            return
        level = 0
        self.edge_level[(u, v)] = 0
        if not self.forests[0].connected(u, v):
            for i in range(0, self.L + 1):
                self.forests[i].link(u, v)
            self.is_tree_edge[(u, v)] = True
            self.comp_count -= 1  # 두 컴포넌트가 합쳐짐
        else:
            self.non_tree_edges[0].add((u, v))
            self.is_tree_edge[(u, v)] = False

    def delete_edge(self, u, v):
        if u > v:
            u, v = v, u
        if (u, v) not in self.edge_level:
            return
        level = self.edge_level[(u, v)]
        del self.edge_level[(u, v)]
        if not self.is_tree_edge[(u, v)]:
            self.non_tree_edges[level].discard((u, v))
            del self.is_tree_edge[(u, v)]
        else:
            for i in range(level, self.L + 1):
                if self.forests[i].connected(u, v):
                    self.forests[i].cut(u, v)
            del self.is_tree_edge[(u, v)]
            replacement = None
            rep_level = None
            for l in range(level, -1, -1):
                for e in list(self.non_tree_edges[l]):
                    x, y = e
                    if not self.forests[l].connected(x, y):
                        replacement = e
                        rep_level = l
                        break
                if replacement is not None:
                    break
            if replacement is not None:
                self.non_tree_edges[rep_level].remove(replacement)
                self.is_tree_edge[replacement] = True
                for i in range(rep_level, self.L + 1):
                    if not self.forests[i].connected(replacement[0], replacement[1]):
                        self.forests[i].link(replacement[0], replacement[1])
            else:
                self.comp_count += 1
            for l in range(level + 1):
                to_promote = []
                for e in list(self.non_tree_edges[l]):
                    x, y = e
                    if self.forests[l].connected(x, y):
                        to_promote.append(e)
                for e in to_promote:
                    self.non_tree_edges[l].remove(e)
                    new_level = l + 1
                    if new_level <= self.L:
                        self.non_tree_edges[new_level].add(e)
                        self.edge_level[e] = new_level
                    else:
                        if e in self.edge_level:
                            del self.edge_level[e]

    def connected(self, u, v):
        return self.forests[0].connected(u, v)

    def get_component_count(self):
        return self.comp_count


def load_network(file_path):
    G = nx.Graph()
    with open(file_path, 'r') as f:
        for line in f:
            if line.startswith('#'):
                continue
            u, v = map(int, line.strip().split())
            G.add_edge(u, v)

    mapping = {}
    for new_label, old_label in enumerate(G.nodes()):
        mapping[old_label] = new_label

    G = nx.relabel_nodes(G, mapping)
    return G




def k_core_seed(G, tau):
    cores = nx.core_number(G)
    k_star = max(cores.values())

    best_k = k
    T = None

    while k <= k_star:
        nodes_k = [node for node, core in cores.items() if core >= k]

        if not nodes_k:
            break

        sub_g = G.subgraph(nodes_k)
        components = list(nx.connected_components(sub_g))

        if not components:
            break

        largest_cc = max(components, key=lambda comp: len(comp))
        T = sub_g.subgraph(largest_cc)

        if math.floor(T.number_of_nodes() ** tau) <= k:
            best_k = k
            print("size of feasible k-core:", k, "-core", T.number_of_nodes())
            break

        k += 1

    k -= 1
    nodes_km1 = [node for node, core in cores.items() if core >= best_k - 1]

    if not nodes_km1:
        return None  

    sub_g_km1 = G.subgraph(nodes_km1)

    if k != k_star:
        for component in nx.connected_components(sub_g_km1):
            if set(T.nodes()).intersection(component):
                final_component = sub_g_km1.subgraph(component)
                return final_component, T, cores,k
    else:
        return [], [],cores,k  


def largest_feasible_connected_component(G, tau):
    cores = nx.core_number(G)
    k_star = max(cores.values())

    k = 2
    best_k = k
    T = None

    while k <= k_star:
        nodes_k = [node for node, core in cores.items() if core >= k]

        if not nodes_k:
            break

        sub_g = G.subgraph(nodes_k)
        components = list(nx.connected_components(sub_g))

        if not components:
            break

        largest_cc = max(components, key=lambda comp: len(comp))
        T = sub_g.subgraph(largest_cc)

        if math.floor(T.number_of_nodes() ** tau) <= k:
            best_k = k
            print("size of feasible k-core:" , k,"-core",  T.number_of_nodes())
            break

        k += 1

    k -= 1
    nodes_km1 = [node for node, core in cores.items() if core >= best_k-1]

    if not nodes_km1:
        return None  

    sub_g_km1 = G.subgraph(nodes_km1)

    if k != k_star:
        for component in nx.connected_components(sub_g_km1):
            if set(T.nodes()).intersection(component):
                final_component = sub_g_km1.subgraph(component)
                return final_component, T
    else:
        return G.subgraph(T), T  # k_star인 경우, 모든 노드가 포함된 컴포넌트 반환



def flexi_clique(G, T, tau):
    start = time.time()
    n = G.number_of_nodes()

    fdc = FullyDynamicConnectivity(n)

    for (u, v) in G.edges:
        fdc.insert_edge(u, v)


    components = list(nx.connected_components(G))
    components.sort(key=lambda comp: len(comp), reverse=True)
    Q = deque(components)

    print(f"initialisation time: {time.time() - start}")

    best_component_size = len(T.nodes())
    best_component = T

    while Q:
        C = Q.popleft()
        if len(C) <= best_component_size:
            continue

        comp_adj = {node: set(G.neighbors(node)).intersection(C) for node in C}
        node_deg = {node: len(neighbors) for node, neighbors in comp_adj.items()}

        candidates = sorted(list(C), key=lambda x: node_deg[x])
        i = 0  # 후보 리스트 내 인덱스


        while i < len(candidates) and len(C) > best_component_size:
            start = time.time()

            threshold = math.floor(len(C) ** tau)
            min_deg = node_deg[candidates[0]]
            candidate = candidates[i]
            if min_deg >= threshold:
                if len(C) > best_component_size:
                    best_component_size = len(C)
                    best_component = set(C)
                break

            candidate_edges = [(candidate, neighbor) for neighbor in comp_adj[candidate]]
            old_nc = fdc.get_component_count()
            for (u, v) in candidate_edges:
                u0, v0 = u, v
                key = (min(u0, v0), max(u0, v0))
                if key in fdc.edge_level:
                    fdc.delete_edge(u0, v0)
            new_nc = fdc.get_component_count()
            diff = new_nc - old_nc

            print(f"deletion time: {time.time() - start}")

            start = time.time()
            if diff == 1:
                print(f"Candidate {candidate} accepted; deleting candidate. remaining nodes: {len(C)}")
                G.remove_node(candidate)
                C.remove(candidate)
                if candidate in comp_adj:
                    del comp_adj[candidate]
                if candidate in node_deg:
                    del node_deg[candidate]
                for node in list(comp_adj.keys()):
                    if candidate  in comp_adj[node]:
                        comp_adj[node].remove(candidate)
                        node_deg[node] -= 1

                candidates = sorted(list(C), key=lambda x: node_deg[x])
                i = 0
            else:
                for (u, v) in candidate_edges:
                    fdc.insert_edge(u, v)
                i += 1
            print(f"insertion time: {time.time() - start}")
    return best_component




if __name__ == "__main__":
    # Parse command line arguments
    parser = argparse.ArgumentParser(description="Top_Down Algorithm for tau-flexi-clique")
    parser.add_argument("--file_path", help="Path to the network file")
    parser.add_argument("--tau", type=float, help="Value of tau")
    args = parser.parse_args()

    file_path = args.file_path+"network.dat"


    G = load_network(file_path)
    G.remove_edges_from(nx.selfloop_edges(G))
    tau = args.tau



    start = time.time()
    G, T = largest_feasible_connected_component(G, tau)
    print("largest feasible connected component: ", T)
    # G = igraph_to_networkx(G)
    mt = time.time()
    mapping2 = {}
    for new_label, old_label in enumerate(G.nodes()):
        mapping2[old_label] = new_label

    G = nx.relabel_nodes(G, mapping2)
    print("mapping time: ", time.time() - mt)

    T_mapped = {mapping2[node] for node in T if node in mapping2}

    result = flexi_clique(G,T, tau)
    print("result: ", result)
    end = time.time()


 
    time = end - start
    # Write results to file
    output_dir = os.path.dirname(args.file_path)
    output_filename = f"{tau}_top_down.dat"
    output_path = os.path.join(output_dir, output_filename)

    with open(output_path, 'w') as output_file:
        
        output_file.write(f"{tau}-clique, running time :  {time}\n")
      
    print(f"Results written to {output_path}")