import Std
import Omega.HyperKernel.Op
import Omega.HyperKernel.Analysis
import Omega.HyperKernel.Closure
import Omega.HyperKernel.SetStructure

namespace Omega.HyperKernel
namespace Geometry

open Analysis
open Closure
open Std
open SetStructure

def dictLookupWord (n : Nat) (dict : Dict n) (target : Op n) : Option (List Nat) :=
  (dict.find? (fun p => p.1 == target)).map Prod.snd

def getOpAt? (n : Nat) (gens : List (Op n)) (idx : Nat) : Option (Op n) :=
  match gens, idx with
  | [], _ => none
  | g :: _, 0 => some g
  | _ :: rest, i + 1 => getOpAt? n rest i

def distanceFromWords (a b : List Nat) : Nat :=
  if a.length ≤ b.length then b.length - a.length else a.length - b.length

def opDistanceByWordLength (n : Nat) (dict : Dict n) (a b : Op n) : Option Nat :=
  match dictLookupWord n dict a, dictLookupWord n dict b with
  | some wa, some wb => some (distanceFromWords wa wb)
  | _, _ => none

/-- Distance matrix indexed by closure list order, using shortest-word lengths as coordinates. -/
def distanceMatrix (n : Nat) (dict : Dict n) : Array (Array Nat) :=
  let entries := dict
  let rows := entries.map (fun p =>
    let lens := entries.map (fun q =>
      match dictLookupWord n dict p.1, dictLookupWord n dict q.1 with
      | some w1, some w2 => distanceFromWords w1 w2
      | _, _ => 0)
    lens.toArray)
  rows.toArray

/-- Curvature from a single commuting square of generators:
`q_{ij}(x)` vs `q_{ji}(x)` measured against edge-length 2. -/
def squareCurvatureAt
    (n : Nat)
    (gens : List (Op n))
    (dict : Dict n)
    (op : Op n)
    (i j : Nat) : Option Int :=
  match getOpAt? n gens i, getOpAt? n gens j with
  | none, _ | _, none => none
  | some gi, some gj =>
      let lhs := Op.comp n gj (Op.comp n gi op)
      let rhs := Op.comp n gi (Op.comp n gj op)
      match opDistanceByWordLength n dict lhs rhs with
      | none => none
      | some d =>
          let dInt : Int := Int.ofNat d
          some (dInt - 2)

/-- Discrete curvature collection: all generator pairs at each discovered operation. -/
def discreteCurvature
    (n : Nat)
    (gens : List (Op n))
    (dict : Dict n) : List Int :=
  let items := dict.map Prod.fst
  let genCount := gens.length
  let indices := List.range genCount
  let rec pairLoop (ops : List (Op n)) (acc : List Int) : List Int :=
    match ops with
    | [] => acc
    | o :: os =>
        let rec inside (is : List Nat) (acc' : List Int) : List Int :=
          match is with
          | [] => acc'
          | i :: is' =>
              let rec jsLoop (js : List Nat) (acc'' : List Int) : List Int :=
                match js with
                | [] => acc''
                | j :: js' =>
                    if i = j then
                      jsLoop js' acc''
                    else
                      match squareCurvatureAt n gens dict o i j with
                      | none => jsLoop js' acc''
                      | some k => jsLoop js' (k :: acc'')
              inside is' (jsLoop is' acc')
        pairLoop os (inside indices acc)
  pairLoop items []

def discreteCurvatureAtLevel
    (n : Nat)
    (gens : List (Op n))
    (dict : Dict n)
    (level : Nat) : List Int :=
  discreteCurvature n gens (filterClosureByWordLength n dict level)

def budgetDiscreteCurvature
    (n : Nat)
    (gens : List (Op n))
    (dict : Dict n)
    (maxLen : Nat) : List (Nat × List Int) :=
  (List.range (maxLen + 1)).map (fun l => (l, discreteCurvatureAtLevel n gens dict l))

end Geometry
end Omega.HyperKernel
