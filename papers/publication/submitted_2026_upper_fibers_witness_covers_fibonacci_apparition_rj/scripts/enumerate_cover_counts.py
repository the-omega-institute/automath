"""Enumerate irredundant and connected set covers for k <= 4.

The manuscript table counts families of nonempty subsets of {1,...,k} that
cover the ground set and are irredundant.  A cover is irredundant when every
edge has a private vertex.  Connectedness is connectedness of the associated
hypergraph on the ground set.
"""

from itertools import combinations


def nonempty_subsets(k):
    vertices = tuple(range(1, k + 1))
    subsets = []
    for size in range(1, k + 1):
        subsets.extend(frozenset(s) for s in combinations(vertices, size))
    return subsets


def covers_ground(family, k):
    return set().union(*family) == set(range(1, k + 1))


def is_irredundant(family):
    for edge in family:
        others = set().union(*(other for other in family if other != edge)) if len(family) > 1 else set()
        if not (set(edge) - others):
            return False
    return True


def is_connected(family, k):
    adjacency = {vertex: set() for vertex in range(1, k + 1)}
    for edge in family:
        for vertex in edge:
            adjacency[vertex].update(edge - {vertex})
    seen = {1}
    stack = [1]
    while stack:
        vertex = stack.pop()
        for neighbor in adjacency[vertex] - seen:
            seen.add(neighbor)
            stack.append(neighbor)
    return len(seen) == k


def counts(k):
    subsets = nonempty_subsets(k)
    irredundant = 0
    connected_irredundant = 0
    for mask in range(1, 1 << len(subsets)):
        family = [subsets[index] for index in range(len(subsets)) if mask & (1 << index)]
        if covers_ground(family, k) and is_irredundant(family):
            irredundant += 1
            if is_connected(family, k):
                connected_irredundant += 1
    return irredundant, connected_irredundant


if __name__ == "__main__":
    print("k I_k CI_k")
    for k in range(1, 5):
        i_k, ci_k = counts(k)
        print(f"{k} {i_k} {ci_k}")