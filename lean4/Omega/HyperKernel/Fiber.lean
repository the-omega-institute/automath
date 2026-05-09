import Std
import Omega.HyperKernel.Op
import Omega.HyperKernel.Analysis
import Omega.HyperKernel.Closure
import Omega.HyperKernel.Pretty
import Omega.HyperKernel.SetStructure

namespace HyperKernel
namespace Fiber

open Analysis
open Closure
open Pretty
open SetStructure

/-- Fold dictionary by rank into fibers. -/
def foldByRank (n : Nat) (dict : Dict n) : List (Nat × List (Op n)) :=
  let ops := dict.map Prod.fst
  let rec insert (acc : List (Nat × List (Op n))) (op : Op n) :
      List (Nat × List (Op n)) :=
    let r := rank op
    match acc with
    | [] => [(r, [op])]
    | (k, cls) :: rest =>
        if k == r then
          (k, op :: cls) :: rest
        else
          (k, cls) :: insert rest op
  ops.foldl insert []

/-- Label difference inside a same-rank fiber.

Returns a list of |word| differences against the first representative.
-/
def fiberLabelDiff (n : Nat) (fiber : List (Op n × Word)) : List Nat :=
  match fiber with
  | [] => []
  | (_op0, w0) :: rest =>
      let base := w0.length
      rest.map (fun p =>
        if p.2.length ≥ base then p.2.length - base else base - p.2.length)

/-- Produce all rank-fibers and their internal label diffs. -/
def rankFiberDiffs (n : Nat) (dict : Dict n) : List (List Nat) :=
  let byRank := foldByRank n dict
  byRank.map (fun p =>
    let r := p.1
    let _ops := p.2
    fiberLabelDiff n ((dict.filter (fun x => rank x.1 == r)).map (fun x => (x.1, x.2)))
  )

def rankFiberDiffsAtLevel (n : Nat) (dict : Dict n) (level : Nat) : List (List Nat) :=
  rankFiberDiffs n (filterClosureByWordLength n dict level)

def budgetRankFiberDiffs (n : Nat) (dict : Dict n) (maxLen : Nat) : List (Nat × List (List Nat)) :=
  (List.range (maxLen + 1)).map (fun l => (l, rankFiberDiffsAtLevel n dict l))

end Fiber
end HyperKernel
