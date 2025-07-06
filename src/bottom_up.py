import networkx as nx
import sys, math
from collections import defaultdict
from collections import deque
import time
import argparse
import heapq
import os
import pandas


def modified_greedy_plus_plus(G, tau):

    candidates = []
    best_flexi = set()
    global_best_size = 0

    comp_heap = [(-len(comp), comp) for comp in nx.connected_components(G)]
    heapq.heapify(comp_heap)

    while comp_heap:
        _, comp = heapq.heappop(comp_heap)
        comp = set(comp)

        min_deg_comp = min(G.degree[node] for node in comp)
        candidate_max_size = math.floor(min_deg_comp ** (1 / tau))
        if candidate_max_size <= global_best_size:
            continue

        subgraph = G.subgraph(comp).copy()
        loads = {node: 0 for node in subgraph.nodes}
        heap = [(loads[node] + degree, node) for node, degree in subgraph.degree]
        heapq.heapify(heap)
        remaining_nodes = set(subgraph.nodes)
        current_degrees = dict(subgraph.degree)

        while remaining_nodes:
            num_nodes = len(remaining_nodes)
            threshold = math.floor(num_nodes ** tau)

            while heap:
                score, node = heapq.heappop(heap)
                if node in remaining_nodes and (loads[node] + current_degrees[node] == score):
                    min_degree = current_degrees[node]
                    break
            # else:
            #     break


            if min_degree >= threshold:
                candidate_set = set(remaining_nodes)
                comps = list(nx.connected_components(G.subgraph(candidate_set)))
                if len(comps) == 1:
                    min_degree_original = min(G.degree[node] for node in candidate_set)
                    if len(candidate_set) > global_best_size:
                        global_best_size = len(candidate_set)
                        best_flexi = candidate_set
                    candidates.append((candidate_set, min_degree_original))
                else:
                    for new_comp in comps:
                        heapq.heappush(comp_heap, (-len(new_comp), new_comp))
                break

            remaining_nodes.remove(node)
            loads[node] += current_degrees[node]
            visited = set()

            for neighbor in list(subgraph.neighbors(node)):
                if neighbor in remaining_nodes and neighbor not in visited:
                    current_degrees[neighbor] -= 1
                    heapq.heappush(heap, (loads[neighbor] + current_degrees[neighbor], neighbor))
                    visited.add(neighbor)

    return best_flexi, global_best_size




def expand_candidates(G, candidates, tau):
    expanded_subgraphs = []

    sorted_candidates = sorted(candidates, key=lambda x: len(x[0]), reverse=True)

    for candidate_set, _ in sorted_candidates:
        expanded_set = set(candidate_set)
        neighbors_to_explore = set(neigh for node in candidate_set for neigh in G.neighbors(node)) - expanded_set


        while neighbors_to_explore:
            neighbors_to_explore = set(sorted(neighbors_to_explore, key=lambda node: G.degree[node], reverse=True))

            new_node = neighbors_to_explore.pop()
            expanded_set.add(new_node)

            subgraph = G.subgraph(expanded_set)
            min_degree = min(subgraph.degree[node] for node in expanded_set)
            threshold = math.floor(len(expanded_set) ** tau)

            if min_degree < threshold:
                expanded_set.remove(new_node)
                break

            neighbors_to_explore.update(set(G.neighbors(new_node)) - expanded_set)

        min_degree_original = min(G.degree[node] for node in expanded_set)
        expanded_subgraphs.append((expanded_set, min_degree_original))

    return expanded_subgraphs





def load_graph(file_path):
    G = nx.Graph()
    with open(file_path, 'r') as f:
        for line in f:
            if line.startswith('#'):
                continue
            u, v = map(int, line.strip().split())
            G.add_edge(u, v)
    return G


if __name__ == "__main__":
    # Parse command line arguments
    parser = argparse.ArgumentParser(description="Top_Down Algorithm for tau-flexi-clique")
    parser.add_argument("--file_path", help="Path to the network file")
    parser.add_argument("--tau", type=float, help="Value of tau")
    args = parser.parse_args()

    file_path = args.file_path+"network.dat"

    G = load_graph(file_path)
    G.remove_edges_from(nx.selfloop_edges(G))
    tau = args.tau

    start = time.time()
    candidates, best_size = modified_greedy_plus_plus(G, tau)
    end_1 = time.time()
    result = expand_candidates(G, candidates, tau)
    end = time.time()


    minimum_degree = min(G.degree[node] for node in result[0][0])
    # Write results to file
    output_dir = os.path.dirname(args.file_path)
    output_filename = f"{tau}_bottom_up.dat"
    output_path = os.path.join(output_dir, output_filename)

    with open(output_path, 'w') as output_file:
        output_file.write(f"{tau}-clique, starting block time :  {end_1-start}\n")
        output_file.write(f"{tau}-clique, total running time :  {end-start}\n")
        # output_file.write(f"{tau}-clique: nodes: {result}\n")
        output_file.write(f"{tau}-clique: # of nodes: {len(result[0][0])}\n")
        output_file.write(f"{tau}-clique: degree threshold: {minimum_degree}\n")

    print(f"Results written to {output_path}")