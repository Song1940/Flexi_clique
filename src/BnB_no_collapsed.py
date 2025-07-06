import networkx as nx
import math
import time
import sys
from collections import deque
import argparse
import os
from top_down import k_core_seed
from bottom_up import modified_greedy_plus_plus


sys.setrecursionlimit(10000)

# Global variables
best_flexiclique = set()
best_size = 0
discarded = set()  # 전역적으로 제거(pruning)된 노드들
node_info = {}  # { node: { 'degree': int, 'neighbors': set(...) } }
initial_order = []  # 초기 정렬 순서 (degree 오름차순, node_info 기준)
theta = 0  # pruning threshold

def preprocess_graph(G):
    """G의 각 노드에 대해 degree와 neighbor 정보를 저장하는 dict 반환."""
    node_info = {}
    for v in G.nodes():
        node_info[v] = {
            'degree': G.degree(v),
            'neighbors': set(G.neighbors(v))
        }
    return node_info

def core_fillter(cores, tau, best_size):
    """
    현재 best_size k에 대해 임계값 T = floor((k+1)^tau)보다 degree가 낮은 노드들을
    연쇄적으로 제거하고, 제거된 노드들을 removed_set에 저장하여 반환.
    """

    theta = (best_size+1)**tau-1
    # if k +1>= theta:
    #     theta = k+1
    print("Pruning threshold:", theta)
    # t-cores
    subgraph = [node for node, core in cores.items() if core > theta]
    print("Initial subgraph size:", len(subgraph))
    return subgraph

def iterative_prune(info, best_size, tau):
    """
    현재 best_size k에 대해 임계값 T = floor((k+1)^tau)보다 degree가 낮은 노드들을
    연쇄적으로 제거하고, 제거된 노드들을 removed_set에 저장하여 반환.
    """
    theta = (best_size+1)**tau-1
    print("Pruning threshold:", theta)

    removed_set = set()
    queue = [v for v in info if info[v]['degree'] <= theta]

    while queue:
        v = queue.pop()
        if v in removed_set:
            continue
        removed_set.add(v)

        for u in info[v]['neighbors']:
            if u in info:
                info[u]['neighbors'].discard(v)
                info[u]['degree'] = len(info[u]['neighbors'])
                if info[u]['degree'] <= theta and u not in removed_set:
                    queue.append(u)

        del info[v]
    return info, removed_set

def is_flexiclique(S, G, tau):
    """
    S에 해당하는 subgraph G[S]가 flexi‐clique 조건, 즉
    모든 노드의 내부 degree가 floor(|S|^tau) 이상인지 확인.
    """
    if not S:
        return False
    k = len(S)
    if k == 1:
        return True
    threshold = math.floor(k ** tau)
    subgraph = G.subgraph(S)
    min_deg = min(dict(subgraph.degree()).values())
    return min_deg >= threshold


def check_pruning_in_S(S, node_info, theta, D):
    # S 내에서 조건에 맞지 않는 항목이 있으면 전체 함수에서 즉시 반환합니다.
    for u in S: #(x for x in S if x in node_info and node_info[x]['degree'] <= theta + len(D) - 1):
        # if u is not in node_info return True, u
        if u not in node_info:
            return True, u
        lost = sum(1 for w in node_info[u]['neighbors'] if w in D)
        if node_info[u]['degree'] - lost <= theta:
            # print("Pruning occurred for node", u)
            return True, u
    return False, None


def find_distance_threshold(theta, tau, degree_v):
    d = 0
    while True:
        f_d = theta + d + 1 + (d // 3) * (theta - 2)
        if math.floor(f_d ** tau) > degree_v:
            return d
        d += 1


def cp_branch_BFS(G, tau):

    global best_flexiclique, best_size, discarded, node_info, initial_order, theta

    queue = deque()
    initial_state = ([], [], [v for v in initial_order if v not in discarded], set())
    queue.append(initial_state)

    while queue:
        S, Cr, Cun, D = queue.popleft()

        bound = len(S) + len(Cr) + len(Cun)
        if bound <= best_size:
            continue

        # 만약 S에 이미 discarded된 노드가 있다면 상태 무시

        if set(S).intersection(discarded):
            continue

        if discarded:
            Cr = [v for v in Cr if v not in discarded]
            Cun = {v for v in Cun if v not in discarded}


        if len(S) == 0:
            R = Cun[:]
        else:
            R = Cr[:]
        if not R:
            continue

        for i, v in enumerate(R):
            # new_S: S에 v 추가 (리스트 덧셈 사용)
            new_S = S + [v]
            # new_D: 이전 branch에서 이미 고려한 후보들 (R의 앞쪽 원소들) 누적
            new_D = D.union(set(R[:i]))

            theta = (best_size+1)**tau-1

            prune_flag,u = check_pruning_in_S(new_S, node_info, theta, new_D)
            if prune_flag:
                if u == v:
                    continue
                else:
                    break


            # 현재 best_size 갱신 검사 best_size = global
            if len(new_S) > best_size and is_flexiclique(new_S, G, tau):
                best_flexiclique = new_S.copy()
                best_size = len(new_S)
                print(f"Updated best_size to {best_size}: {sorted(best_flexiclique)}")
                if math.floor((best_size+1)**tau-1) > theta:
                    node_info, removed_nodes = iterative_prune(node_info, best_size, tau)
                    discarded = set(G.nodes()) - set(node_info.keys())
                    new_D = new_D.union(discarded)
                    prev_D = new_D
                    print("Global discarded updated:", len(discarded))

                if set(S).intersection(new_D):
                    break
                if set(new_S).intersection(new_D):
                    continue


            # Cr 업데이트: 기존 Cr에서 new_S와 new_D에 있는 노드들을 제거
            old_cr_filtered = [x for x in Cr if x not in set(new_S) and x not in new_D]
            # v의 이웃들 중, 아직 new_S, new_D, old_cr_filtered에 없는 노드들을, node_info에서 degree 기준으로 정렬
            new_neighbors = sorted(
                [w for w in node_info[v]['neighbors'] if
                 w not in set(new_S) and w not in new_D and w not in old_cr_filtered],
                key=lambda x: node_info[x]['degree']
            )
            new_Cr = old_cr_filtered + new_neighbors

            # new_Cun: 기존 Cun에서 new_S, new_Cr, new_D에 속한 노드들을 제거 (리스트로 변환)
            new_Cun = list((set(Cun) - set(new_S) - set(new_Cr) - new_D))

            if len(new_S) + len(new_Cr) + len(new_Cun) <= best_size:
                break

            # # Rule 3
            # if len(new_S) == 1:
            #     union_nodes = (set(new_S) | set(new_Cr) | set(new_Cun))
            #     induced_subgraph = G.subgraph(union_nodes)
            #     min_deg = min(induced_subgraph.degree(n) for n in new_S)
            #
            #     sssp = nx.single_source_shortest_path_length(induced_subgraph, v)
            #
            #     new_Cun = {u for u in new_Cun if u in sssp}
            #
            #     d_star = find_distance_threshold(theta, tau, min_deg)
            #
            #     new_Cun = {u for u in new_Cun if sssp[u] < d_star}
            #     # print node that is farer than d_star
            #     pruned = {v for v in new_Cun if sssp[v] >= d_star}
            #     if pruned:
            #         print("Pruning occurred for node", pruned)

            if len(new_S) + len(new_Cr) + len(new_Cun) <= best_size:
                continue


            print(f"Branching on {v}: new_S={len(new_S)}, |new_Cr|={len(new_Cr)}, |new_Cun|={len(new_Cun)}, |new_D| = {len(new_D)}, best_size={best_size}")
            queue.append((new_S, new_Cr, new_Cun, new_D))


def find_max_flexiclique(G, tau):
    """
    주어진 그래프 G와 파라미터 tau에 대해 최대 flexi‐clique를 찾습니다.
    전처리 후 node_info와 초기 정렬 순서를 고정합니다.
    """
    global best_flexiclique, best_size, discarded, node_info, initial_order, theta
    best_flexiclique = set()

    cores = nx.core_number(G)

    cand, size = modified_greedy_plus_plus(G, tau)

    print("candidate size", size)

    sub = cand

    F = G.subgraph(sub)

    print("minimum degree:", min(dict(F.degree()).values()))
    print("F' size", len(F.nodes()))

    best_size = size 
    print("Initial best size:", best_size)
    initial_best_size = best_size

    print("Threshold", math.floor((best_size ** tau)))

    H = core_fillter(cores, tau, best_size)
    # densest subgraph of H
    print("max corness", max(cores.values()))
    for i in sub:
        print(i, cores[i])


    H = G.subgraph(H)
    #articulation nodes
    print("min degree of filltered grpah: ", min(dict(H.degree()).values()))

    print("possible maximum size:", math.floor((max(cores.values())+1)**(1/tau)))
    # return None, None

    node_info = preprocess_graph(H)

    initial_order = sorted(list(node_info.keys()), key=lambda v: node_info[v]['degree'])
    cp_branch_BFS(H, tau)
    print("best flexi clique:", best_flexiclique)
    return best_flexiclique, best_size, initial_best_size


def load_network(file_path):
    """파일에서 네트워크 데이터를 읽어 NetworkX 그래프로 반환."""
    G = nx.Graph()
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            # 빈 줄 혹은 주석(#)이면 건너뛰기
            if not line or line.startswith('#'):
                continue

            parts = line.split()
            # 토큰이 2개 미만이면 역시 무시
            if len(parts) < 2:
                continue

            u, v = map(int, parts[:2])
            G.add_edge(u, v)
    return G





if __name__ == "__main__":
    # Parse command line arguments
    parser = argparse.ArgumentParser(description="BnB Algorithm for tau-flexi-clique")
    parser.add_argument("--file_path", help="Path to the network file")
    parser.add_argument("--tau", type=float, help="Value of tau")
    args = parser.parse_args()

    file_path = args.file_path+"network.dat"


    G = load_network(file_path)
    G.remove_edges_from(nx.selfloop_edges(G))

    tau = args.tau

    ## 휴리스틱하게 best size 구하기

    ## 1차 filtering

    ## 남은 노드들로 만든 induced subgraph에서 all pairs shortest path 구하기

    ## 그 dataframe 과 함께 find_max_flexiclique 호출하기



    start = time.time()
    result, size, initial_best_size = find_max_flexiclique(G, tau)
    end = time.time()

    # subgraph = G.subgraph(result)
    # minimum_degree = min(subgraph.degree(v) for v in subgraph)
    # subgraph_nodes = sorted(subgraph.nodes())
    # subgraph_edges = sorted(subgraph.edges())

    time = end - start
    # Write results to file
    output_dir = os.path.dirname(args.file_path)
    output_filename = f"{tau}_BnB_no_collapse.dat"
    output_path = os.path.join(output_dir, output_filename)

    with open(output_path, 'w') as output_file:
        # output_file.write(f"node : {subgraph_nodes}\n")
        # output_file.write(f"edge : {subgraph_edges}\n")
        output_file.write(f"{tau}-clique, running time :  {time}\n")
        output_file.write(f"{tau}-clique: nodes: {result}\n")
        output_file.write(f"{tau}-clique: # of nodes: {size}\n")
        output_file.write(f"{tau}-clique: initial best size: {initial_best_size}\n")
        # output_file.write(f"{tau}-clique: min degree: {minimum_degree}\n")
        # output_file.write(f"{tau}-clique: # of components: {nx.number_connected_components(subgraph)}\n")

    print(f"Results written to {output_path}")