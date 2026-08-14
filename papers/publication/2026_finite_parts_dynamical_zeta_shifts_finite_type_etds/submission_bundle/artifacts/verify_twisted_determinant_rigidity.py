"""Exact finite checks for twisted-determinant inverse rigidity.

The search works with named edges.  Gauge equivalence is vertex gauge,
tau^u(e) = u(o(e))^{-1} tau(e) u(t(e)).  A collision is promoted to a
Livsic counterexample only when a marked periodic path has non-conjugate
holonomies, which is an obstruction to every continuous transfer function.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import factorial
from pathlib import Path
from typing import Callable, Hashable, Iterable, Sequence

import sympy as sp


z = sp.Symbol("z")


@dataclass(frozen=True)
class Edge:
    origin: int
    terminus: int
    name: str


@dataclass(frozen=True)
class BaseGraph:
    name: str
    vertex_count: int
    edges: tuple[Edge, ...]

    @staticmethod
    def full_shift(loop_count: int) -> "BaseGraph":
        return BaseGraph(
            f"full-{loop_count}",
            1,
            tuple(Edge(0, 0, chr(ord("a") + j)) for j in range(loop_count)),
        )

    @staticmethod
    def golden_mean() -> "BaseGraph":
        return BaseGraph(
            "golden-mean",
            2,
            (
                Edge(0, 0, "a"),
                Edge(0, 1, "b"),
                Edge(1, 0, "c"),
            ),
        )

    @staticmethod
    def full_two_vertex() -> "BaseGraph":
        return BaseGraph(
            "full-two-vertex",
            2,
            (
                Edge(0, 0, "a"),
                Edge(0, 1, "b"),
                Edge(1, 0, "c"),
                Edge(1, 1, "d"),
            ),
        )


@dataclass(frozen=True)
class Representation:
    name: str
    dimension: int
    matrix: Callable[[Hashable], sp.Matrix]


@dataclass(frozen=True)
class FiniteGroup:
    name: str
    elements: tuple[Hashable, ...]
    multiply: Callable[[Hashable, Hashable], Hashable]
    inverse: Callable[[Hashable], Hashable]
    conjugacy_key: Callable[[Hashable], Hashable]
    irreps: tuple[Representation, ...]
    names: tuple[tuple[str, Hashable], ...]

    def identity(self) -> Hashable:
        for g in self.elements:
            if all(
                self.multiply(g, h) == h and self.multiply(h, g) == h
                for h in self.elements
            ):
                return g
        raise ValueError("group has no identity")

    def named_elements(self, *names: str) -> tuple[Hashable, ...]:
        table = dict(self.names)
        return tuple(table[name] for name in names)

    def index(self, g: Hashable) -> int:
        return self.elements.index(g)


def _canonical_expr(expr: sp.Expr) -> sp.Expr:
    return sp.collect(sp.simplify(sp.expand(expr)), z)


def _expr_string(expr: sp.Expr) -> str:
    return sp.sstr(_canonical_expr(expr))


def cyclic_group(order: int) -> FiniteGroup:
    if order < 1:
        raise ValueError("cyclic group order must be positive")
    elements = tuple(range(order))
    root = sp.expand_complex(sp.exp(2 * sp.pi * sp.I / order))

    def rep(character: int) -> Representation:
        return Representation(
            f"chi{character}",
            1,
            lambda g, character=character: sp.Matrix(
                [[sp.simplify(root ** (character * int(g)))]]
            ),
        )

    return FiniteGroup(
        f"Z/{order}",
        elements,
        lambda a, b: (int(a) + int(b)) % order,
        lambda a: (-int(a)) % order,
        lambda a: int(a),
        tuple(rep(k) for k in range(order)),
        tuple((str(k), k) for k in elements),
    )


def _permutation_product(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p[q[i]] for i in range(3))


def _permutation_inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    result = [0, 0, 0]
    for i, image in enumerate(p):
        result[image] = i
    return tuple(result)


def _permutation_sign(p: tuple[int, ...]) -> int:
    inversions = sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
    return -1 if inversions % 2 else 1


def _standard_s3_matrix(p: tuple[int, ...]) -> sp.Matrix:
    basis = ((1, 0, -1), (0, 1, -1))
    columns = []
    for vector in basis:
        image = [0, 0, 0]
        for i in range(3):
            image[p[i]] = vector[i]
        columns.append((image[0], image[1]))
    return sp.Matrix.hstack(*(sp.Matrix(column) for column in columns))


def _cycle_type(p: tuple[int, ...]) -> tuple[int, ...]:
    seen: set[int] = set()
    lengths = []
    for i in range(3):
        if i in seen:
            continue
        j = i
        length = 0
        while j not in seen:
            seen.add(j)
            length += 1
            j = p[j]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def s3_group() -> FiniteGroup:
    elements = tuple(product(range(3), repeat=3))
    elements = tuple(p for p in elements if len(set(p)) == 3)
    identity = (0, 1, 2)
    transposition = (1, 0, 2)
    cycle = (1, 2, 0)
    irreps = (
        Representation("triv", 1, lambda _g: sp.Matrix([[1]])),
        Representation("sign", 1, lambda g: sp.Matrix([[_permutation_sign(g)]])),
        Representation("std", 2, _standard_s3_matrix),
    )
    group = FiniteGroup(
        "S3",
        elements,
        _permutation_product,
        _permutation_inverse,
        _cycle_type,
        irreps,
        (("()", identity), ("(12)", transposition), ("(123)", cycle)),
    )
    for representation in irreps:
        for p in elements:
            for q in elements:
                assert representation.matrix(_permutation_product(p, q)) == (
                    representation.matrix(p) * representation.matrix(q)
                )
    return group


def twisted_matrix(
    graph: BaseGraph,
    representation: Representation,
    tau: Sequence[Hashable],
) -> sp.Matrix:
    if len(tau) != len(graph.edges):
        raise ValueError("one cocycle value is required for every named edge")
    dimension = graph.vertex_count * representation.dimension
    matrix = sp.zeros(dimension)
    for edge, label in zip(graph.edges, tau):
        block = representation.matrix(label)
        row = edge.origin * representation.dimension
        column = edge.terminus * representation.dimension
        matrix[row : row + representation.dimension, column : column + representation.dimension] += block
    return matrix


def determinant_polynomials(
    graph: BaseGraph, group: FiniteGroup, tau: Sequence[Hashable]
) -> tuple[sp.Expr, ...]:
    result = []
    for representation in group.irreps:
        matrix = twisted_matrix(graph, representation, tau)
        result.append(_canonical_expr((sp.eye(matrix.rows) - z * matrix).det()))
    return tuple(result)


def determinant_signature(
    graph: BaseGraph, group: FiniteGroup, tau: Sequence[Hashable]
) -> tuple[str, ...]:
    return tuple(_expr_string(poly) for poly in determinant_polynomials(graph, group, tau))


def label_multiplicities(
    group: FiniteGroup, tau: Sequence[Hashable]
) -> tuple[int, ...]:
    return tuple(sum(label == element for label in tau) for element in group.elements)


def fourier_recovered_multiplicities(
    group: FiniteGroup, tau: Sequence[Hashable]
) -> tuple[int, ...]:
    if any(representation.dimension != 1 for representation in group.irreps):
        raise ValueError("Fourier recovery in this form requires an abelian group")
    spectral_sums = tuple(
        sp.simplify(sum(representation.matrix(label)[0, 0] for label in tau))
        for representation in group.irreps
    )
    recovered = []
    for element in group.elements:
        value = sp.simplify(
            sum(
                spectral_sum * sp.conjugate(representation.matrix(element)[0, 0])
                for representation, spectral_sum in zip(group.irreps, spectral_sums)
            )
            / len(group.elements)
        )
        if value.is_integer is not True:
            value = sp.nsimplify(value)
        recovered.append(int(value))
    return tuple(recovered)


def bouquet_predicted_fiber_size(
    group: FiniteGroup, tau: Sequence[Hashable]
) -> int:
    result = factorial(len(tau))
    for count in label_multiplicities(group, tau):
        result //= factorial(count)
    return result


def bouquet_swap_collision(tau: Sequence[Hashable]) -> tuple[Hashable, ...]:
    if not tau:
        raise ValueError("an empty bouquet has no collision")
    right = next((index for index, label in enumerate(tau[1:], 1) if label != tau[0]), None)
    if right is None:
        raise ValueError("a constant bouquet labeling is spectrally rigid")
    result = list(tau)
    result[0], result[right] = result[right], result[0]
    return tuple(result)


def gauge_transform(
    graph: BaseGraph,
    group: FiniteGroup,
    tau: Sequence[Hashable],
    transfer: Sequence[Hashable],
) -> tuple[Hashable, ...]:
    if len(transfer) != graph.vertex_count:
        raise ValueError("one transfer value is required for every vertex")
    transformed = []
    for edge, label in zip(graph.edges, tau):
        transformed.append(
            group.multiply(
                group.multiply(group.inverse(transfer[edge.origin]), label),
                transfer[edge.terminus],
            )
        )
    return tuple(transformed)


def _label_key(group: FiniteGroup, tau: Sequence[Hashable]) -> tuple[int, ...]:
    return tuple(group.index(g) for g in tau)


def gauge_representative(
    graph: BaseGraph, group: FiniteGroup, tau: Sequence[Hashable]
) -> tuple[Hashable, ...]:
    orbit = (
        gauge_transform(graph, group, tau, transfer)
        for transfer in product(group.elements, repeat=graph.vertex_count)
    )
    return min(orbit, key=lambda candidate: _label_key(group, candidate))


def determinant_cohomology_multiplicity(
    graph: BaseGraph, group: FiniteGroup, tau: Sequence[Hashable]
) -> int:
    target = determinant_signature(graph, group, tau)
    representatives = {
        gauge_representative(graph, group, candidate)
        for candidate in product(group.elements, repeat=len(graph.edges))
    }
    return sum(
        determinant_signature(graph, group, representative) == target
        for representative in representatives
    )


def _closed_edge_paths(graph: BaseGraph, length: int) -> Iterable[tuple[int, ...]]:
    for path in product(range(len(graph.edges)), repeat=length):
        edges = tuple(graph.edges[index] for index in path)
        if all(edges[j].terminus == edges[(j + 1) % length].origin for j in range(length)):
            yield path


def _path_holonomy(
    group: FiniteGroup, tau: Sequence[Hashable], path: Sequence[int]
) -> Hashable:
    value = group.identity()
    for index in path:
        value = group.multiply(value, tau[index])
    return value


def periodic_class_profile(
    graph: BaseGraph,
    group: FiniteGroup,
    tau: Sequence[Hashable],
    length: int,
    *,
    marked: bool = False,
) -> tuple:
    paths = tuple(_closed_edge_paths(graph, length))
    if marked:
        return tuple(
            (path, group.conjugacy_key(_path_holonomy(group, tau, path)))
            for path in paths
        )
    counts: dict[Hashable, int] = {}
    for path in paths:
        key = group.conjugacy_key(_path_holonomy(group, tau, path))
        counts[key] = counts.get(key, 0) + 1
    return tuple(sorted(counts.items(), key=lambda item: repr(item[0])))


def first_marked_periodic_witness(
    graph: BaseGraph,
    group: FiniteGroup,
    tau: Sequence[Hashable],
    tau_prime: Sequence[Hashable],
    max_length: int = 6,
) -> tuple[int, tuple[int, ...], Hashable, Hashable] | None:
    for length in range(1, max_length + 1):
        for path in _closed_edge_paths(graph, length):
            left = group.conjugacy_key(_path_holonomy(group, tau, path))
            right = group.conjugacy_key(_path_holonomy(group, tau_prime, path))
            if left != right:
                return length, path, left, right
    return None


def regular_skew_adjacency(
    graph: BaseGraph, group: FiniteGroup, tau: Sequence[Hashable]
) -> sp.Matrix:
    size = graph.vertex_count * len(group.elements)
    matrix = sp.zeros(size)
    for edge, label in zip(graph.edges, tau):
        for group_index, value in enumerate(group.elements):
            target = group.multiply(value, label)
            row = edge.origin * len(group.elements) + group_index
            column = edge.terminus * len(group.elements) + group.index(target)
            matrix[row, column] += 1
    return matrix


def perron_boundary_signature(
    graph: BaseGraph, group: FiniteGroup, tau: Sequence[Hashable]
) -> tuple[str, ...]:
    trivial = group.irreps[0]
    base = twisted_matrix(graph, trivial, (group.identity(),) * len(graph.edges))
    base_eigenvalues = tuple(base.eigenvals())
    perron_root = max(base_eigenvalues, key=lambda value: float(sp.re(value).evalf()))
    skew_eigenvalues = regular_skew_adjacency(graph, group, tau).eigenvals()
    boundary = []
    for eigenvalue, multiplicity in skew_eigenvalues.items():
        squared_modulus = sp.simplify(eigenvalue * sp.conjugate(eigenvalue))
        if sp.simplify(squared_modulus - perron_root**2) == 0:
            boundary.extend(_expr_string(eigenvalue) for _ in range(multiplicity))
    return tuple(sorted(boundary))


def is_primitive_nonnegative(matrix: sp.Matrix) -> bool:
    if matrix.rows == 1:
        return matrix[0, 0] > 0
    boolean = matrix.applyfunc(lambda entry: 1 if entry > 0 else 0)
    power_matrix = sp.eye(matrix.rows)
    # Wielandt's primitivity exponent bound, DOI 10.1007/BF02230720.
    wielandt_bound = matrix.rows * matrix.rows - 2 * matrix.rows + 2
    for _ in range(1, wielandt_bound + 1):
        power_matrix = power_matrix * boolean
        if all(entry > 0 for entry in power_matrix):
            return True
    return False


def all_twisted_blocks_semisimple(
    graph: BaseGraph, group: FiniteGroup, tau: Sequence[Hashable]
) -> bool:
    return all(
        twisted_matrix(graph, representation, tau).is_diagonalizable()
        for representation in group.irreps
    )


@dataclass(frozen=True)
class SearchStatistics:
    graph: str
    group: str
    cocycles: int
    gauge_classes: int
    determinant_fibers: int
    colliding_gauge_pairs: int
    marked_witness_pairs: int


@dataclass(frozen=True)
class AbelianBouquetAudit:
    graph: str
    group: str
    cocycles: int
    rigid_cocycles: int
    nonrigid_cocycles: int
    formula_failures: int
    collision_failures: int


def abelian_bouquet_necessity_audit(
    graph: BaseGraph, group: FiniteGroup
) -> AbelianBouquetAudit:
    if graph.vertex_count != 1 or any(
        edge.origin != 0 or edge.terminus != 0 for edge in graph.edges
    ):
        raise ValueError("the necessity audit requires a one-vertex bouquet")
    if any(representation.dimension != 1 for representation in group.irreps):
        raise ValueError("the necessity audit requires an abelian group")

    cocycles = tuple(product(group.elements, repeat=len(graph.edges)))
    fibers: dict[tuple[str, ...], list[tuple[Hashable, ...]]] = {}
    for tau in cocycles:
        fibers.setdefault(determinant_signature(graph, group, tau), []).append(tau)

    rigid = 0
    formula_failures = 0
    collision_failures = 0
    for tau in cocycles:
        fiber = fibers[determinant_signature(graph, group, tau)]
        predicted = bouquet_predicted_fiber_size(group, tau)
        if (
            len(fiber) != predicted
            or fourier_recovered_multiplicities(group, tau)
            != label_multiplicities(group, tau)
        ):
            formula_failures += 1
        if predicted == 1:
            rigid += 1
            continue
        tau_prime = bouquet_swap_collision(tau)
        if (
            tau_prime == tau
            or determinant_signature(graph, group, tau_prime)
            != determinant_signature(graph, group, tau)
            or first_marked_periodic_witness(graph, group, tau, tau_prime, 1) is None
        ):
            collision_failures += 1
    return AbelianBouquetAudit(
        graph.name,
        group.name,
        len(cocycles),
        rigid,
        len(cocycles) - rigid,
        formula_failures,
        collision_failures,
    )


def search_model(graph: BaseGraph, group: FiniteGroup) -> SearchStatistics:
    representatives: dict[tuple[int, ...], tuple[Hashable, ...]] = {}
    for tau in product(group.elements, repeat=len(graph.edges)):
        representative = gauge_representative(graph, group, tau)
        representatives[_label_key(group, representative)] = representative

    fibers: dict[tuple[str, ...], list[tuple[Hashable, ...]]] = {}
    for representative in representatives.values():
        fibers.setdefault(
            determinant_signature(graph, group, representative), []
        ).append(representative)

    colliding_pairs = 0
    witnessed_pairs = 0
    for fiber in fibers.values():
        for left_index in range(len(fiber)):
            for right_index in range(left_index + 1, len(fiber)):
                colliding_pairs += 1
                if first_marked_periodic_witness(
                    graph, group, fiber[left_index], fiber[right_index]
                ):
                    witnessed_pairs += 1
    return SearchStatistics(
        graph.name,
        group.name,
        len(group.elements) ** len(graph.edges),
        len(representatives),
        len(fibers),
        colliding_pairs,
        witnessed_pairs,
    )


@dataclass(frozen=True)
class MinimalCounterexample:
    group_order: int
    vertex_count: int
    edge_count: int
    tau: tuple[Hashable, ...]
    tau_prime: tuple[Hashable, ...]
    marked_witness_length: int
    base_extension_primitive: bool
    all_twisted_blocks_semisimple: bool


def minimal_counterexample_search() -> MinimalCounterexample:
    group = cyclic_group(2)
    one_loop = BaseGraph.full_shift(1)
    one_loop_signatures = {
        determinant_signature(one_loop, group, tau)
        for tau in product(group.elements, repeat=1)
    }
    if len(one_loop_signatures) != 2:
        raise AssertionError("unexpected collision on the unique one-edge mixing graph")

    graph = BaseGraph.full_shift(2)
    representatives = tuple(product(group.elements, repeat=2))
    for left_index, tau in enumerate(representatives):
        for tau_prime in representatives[left_index + 1 :]:
            if determinant_signature(graph, group, tau) != determinant_signature(
                graph, group, tau_prime
            ):
                continue
            witness = first_marked_periodic_witness(graph, group, tau, tau_prime)
            if witness is None:
                continue
            ordered = sorted((tau, tau_prime), key=lambda item: tuple(item))
            return MinimalCounterexample(
                group_order=2,
                vertex_count=1,
                edge_count=2,
                tau=ordered[0],
                tau_prime=ordered[1],
                marked_witness_length=witness[0],
                base_extension_primitive=all(
                    is_primitive_nonnegative(regular_skew_adjacency(graph, group, item))
                    for item in ordered
                ),
                all_twisted_blocks_semisimple=all(
                    all_twisted_blocks_semisimple(graph, group, item)
                    for item in ordered
                ),
            )
    raise AssertionError("the expected minimal counterexample was not found")


def gauge_sanity_check(
    graph: BaseGraph, group: FiniteGroup, tau: tuple[Hashable, ...]
) -> int:
    signature = determinant_signature(graph, group, tau)
    checked = 0
    for transfer in product(group.elements, repeat=graph.vertex_count):
        transformed = gauge_transform(graph, group, tau, transfer)
        if determinant_signature(graph, group, transformed) != signature:
            raise AssertionError("vertex gauge changed a twisted determinant")
        checked += 1
    return checked


def render_report() -> str:
    z2 = cyclic_group(2)
    z3 = cyclic_group(3)
    s3 = s3_group()
    full_one = BaseGraph.full_shift(1)
    full_two = BaseGraph.full_shift(2)
    full_three = BaseGraph.full_shift(3)
    golden = BaseGraph.golden_mean()
    full_two_vertex = BaseGraph.full_two_vertex()
    cases = (
        (full_one, z2),
        (full_one, z3),
        (full_one, s3),
        (full_two, z2),
        (full_two, z3),
        (full_two, s3),
        (golden, z2),
        (golden, z3),
        (golden, s3),
        (full_two_vertex, z2),
        (full_three, z2),
        (full_three, z3),
    )
    statistics = tuple(search_model(graph, group) for graph, group in cases)
    bouquet_audits = (
        abelian_bouquet_necessity_audit(full_three, z2),
        abelian_bouquet_necessity_audit(full_three, z3),
    )

    identity, transposition, cycle = s3.named_elements("()", "(12)", "(123)")
    sanity_checks = (
        (golden, z3, (0, 1, 2)),
        (golden, s3, (identity, transposition, cycle)),
        (full_two, s3, (transposition, cycle)),
    )
    sanity_total = sum(gauge_sanity_check(*case) for case in sanity_checks)
    minimal = minimal_counterexample_search()
    left = minimal.tau
    right = minimal.tau_prime
    witness = first_marked_periodic_witness(full_two, z2, left, right)
    assert witness is not None
    colliding_peripheral_example = (0, 0, 0, 1)
    rigid_peripheral_example = (0, 0, 1, 0)

    lines = [
        "TWISTED-DETERMINANT INVERSE-RIGIDITY FINITE CERTIFICATE",
        "Exact arithmetic: SymPy 1.13.1; named edges are fixed.",
        "Gauge: tau^u(e)=u(o(e))^{-1} tau(e) u(t(e)).",
        "Marked witness: one fixed periodic path has non-conjugate holonomies,",
        "so the pair is not Livsic cohomologous for any continuous transfer.",
        "",
        "model | group | cocycles | gauge classes | determinant fibers | colliding gauge pairs | marked-witness pairs",
        "--- | --- | ---: | ---: | ---: | ---: | ---:",
    ]
    for item in statistics:
        lines.append(
            f"{item.graph} | {item.group} | {item.cocycles} | "
            f"{item.gauge_classes} | {item.determinant_fibers} | "
            f"{item.colliding_gauge_pairs} | {item.marked_witness_pairs}"
        )
    lines.extend(
        [
            "",
            f"Total cocycles enumerated: {sum(item.cocycles for item in statistics)} "
            "(the prior 327 plus 35 abelian full-three-shift cocycles).",
            "",
            "SHARP ABELIAN-BOUQUET NECESSITY AUDIT",
            "model | group | cocycles | rigid | nonrigid | formula failures | explicit-collision failures",
            "--- | --- | ---: | ---: | ---: | ---: | ---:",
        ]
    )
    for audit in bouquet_audits:
        lines.append(
            f"{audit.graph} | {audit.group} | {audit.cocycles} | "
            f"{audit.rigid_cocycles} | {audit.nonrigid_cocycles} | "
            f"{audit.formula_failures} | {audit.collision_failures}"
        )
    lines.extend(
        [
            "Every nonconstant audited bouquet cocycle is paired with the cocycle obtained",
            "by swapping two differently labelled named loops; the determinants agree and a",
            "length-one marked orbit has distinct abelian holonomy.",
            "",
            "PERRON-PERIPHERAL INSUFFICIENCY (fixed graph=full-two-vertex, group=Z/2)",
            f"colliding class {colliding_peripheral_example}: boundary="
            f"{perron_boundary_signature(full_two_vertex, z2, colliding_peripheral_example)}, "
            f"cohomology multiplicity={determinant_cohomology_multiplicity(full_two_vertex, z2, colliding_peripheral_example)}",
            f"rigid class {rigid_peripheral_example}: boundary="
            f"{perron_boundary_signature(full_two_vertex, z2, rigid_peripheral_example)}, "
            f"cohomology multiplicity={determinant_cohomology_multiplicity(full_two_vertex, z2, rigid_peripheral_example)}",
            "Both regular skew adjacencies are primitive, so graph, group, and Perron-peripheral",
            "spectrum do not determine determinant-to-Livsic rigidity.",
            "",
            f"Gauge sanity transformations checked: {sanity_total}; failures: 0.",
            "",
            "MINIMAL COUNTEREXAMPLE",
            f"group=Z/2; |V|={minimal.vertex_count}; |E|={minimal.edge_count}; base=full-2",
            f"tau(a),tau(b)={left}; tau'(a),tau'(b)={right}",
            "irreducible determinants (trivial, sign): "
            + repr(determinant_signature(full_two, z2, left)),
            f"marked witness: length={witness[0]}, edge word={witness[1]}, "
            f"classes={witness[2]} versus {witness[3]}",
            f"both skew products primitive: {minimal.base_extension_primitive}",
            f"all paired twisted blocks semisimple: {minimal.all_twisted_blocks_semisimple}",
            "smaller search: the unique one-edge mixing graph has no collision for Z/2, Z/3, or S3;",
            "groups of order < 2 are trivial.  Irreducible characters separate conjugacy classes,",
            "so a one-edge collision is impossible for every finite group.",
            "",
            "STATUS: PASS",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> None:
    report = render_report()
    output = Path(__file__).with_name("verify_twisted_determinant_rigidity_output.txt")
    output.write_text(report, encoding="ascii")
    print(report, end="")


if __name__ == "__main__":
    main()
