module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelBase
public import CFSG.Certificates.Kernel.Common.StrSplit
public import Certificates.Kernel.Sporadic.RawGen
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Search
import all Init.Data.List.SplitOn.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.EvenSporG24

open String CFSG.KC.Str CFSG.EvenSporadicStandard.G24Model

@[expose] def g24Text : String :=
  include_str "../../../CFSG/LocalAnalysis/EvenSporadicStandard/Induction/Rows/G24ModelTbl.txt"

end CertificateChecks.EvenSporG24

set_option maxRecDepth 400000 in
#ks_chars CertificateChecks.EvenSporG24.G24T CertificateChecks.EvenSporG24.g24Text

namespace CertificateChecks.EvenSporG24

open String CFSG.KC.Str CFSG.EvenSporadicStandard.G24Model

@[expose] def goodK (p : List Char) : Bool :=
  (!p.isEmpty && p.all Char.isDigit) ||
    (p.getLast?.any (fun c => c.toNat == 10) && !p.dropLast.isEmpty && p.dropLast.all Char.isDigit)

@[expose] def tokV (p : List Char) : Nat := decVal (p.filter Char.isDigit)

theorem ws_false {c : Char} (h : c.isDigit = true) : c.isWhitespace = false := by
  rcases hc : c.isWhitespace with _ | _
  · rfl
  · simp only [Char.isWhitespace, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with ((h1 | h1) | h1) | h1 <;> subst h1 <;> exact absurd h (by decide)

theorem slice_toNat? {u : Slice} {ds : List Char} (hu : u.copy.toList = ds) (hne : ds ≠ [])
    (hd : ∀ c ∈ ds, c.isDigit = true) : u.toNat? = some (decVal ds) := by
  simp only [Slice.toNat?, Slice.isNat]
  simp only [Slice.forIn_eq_forIn_toList, Slice.foldl_eq_foldl_toList, hu]
  rw [forIn_yield (y := ((none : Option Bool), true)) ds]
  · simp only [hne, ↓reduceIte]
    split
    · exact congrArg some (foldl_congr _ _ ds 0 fun x hx n => by simp [ne_underscore (hd x hx)])
    · rename_i h
      exact absurd rfl h
  · intro c hc x
    simp [ne_underscore (hd c hc), hd c hc]
    rfl

theorem start_false {p : List Char} (hne : p ≠ []) (hd : ∀ c ∈ p, c.isDigit = true) :
    (String.ofList p).toSlice.startsWith Char.isWhitespace = false := by
  rw [Slice.startsWith_bool_eq_head?, copy_toSlice, toList_ofList]
  cases p with
  | nil => exact absurd rfl hne
  | cons c cs => simp [ws_false (hd c (by simp))]

theorem split_nl {D T ds : List Char} (h : D ++ T = ds ++ ['\n'])
    (hT : T.all Char.isWhitespace = true) (hD : D.getLast?.any Char.isWhitespace = false)
    (hds : ∀ c ∈ ds, c.isDigit = true) : D = ds := by
  rcases List.eq_nil_or_concat T with rfl | ⟨T', x, rfl⟩
  · rw [List.append_nil] at h
    subst h
    simp [Char.isWhitespace] at hD
  · rw [List.concat_eq_append, ← List.append_assoc] at h
    rw [List.concat_eq_append] at hT
    obtain ⟨h1, -⟩ := List.append_inj' h rfl
    rcases List.eq_nil_or_concat T' with rfl | ⟨T'', y, rfl⟩
    · simpa using h1
    · exfalso
      rw [List.concat_eq_append] at h1 hT
      have hy : y ∈ ds := by rw [← h1]; simp
      have hyw : y.isWhitespace = true := by
        simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true] at hT
        exact hT.1.2
      rw [ws_false (hds y hy)] at hyw
      exact absurd hyw (by decide)

theorem tok_eq {p : List Char} (h : goodK p = true) :
    (String.ofList p).trimAscii.toNat? = some (tokV p) := by
  change (((String.ofList p).toSlice.dropWhile Char.isWhitespace).dropEndWhile
    Char.isWhitespace).toNat? = _
  simp only [goodK, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  rcases h with ⟨hne, hd⟩ | ⟨⟨hl, hne⟩, hd⟩
  · rw [Slice.dropWhile_eq_self (start_false hne hd), dropEndWhile_toSlice,
      dropEndWhile_eq_toSlice]
    · rw [tokV, List.filter_eq_self.2 (fun c hc => hd c hc)]
      exact slice_toNat? (by rw [copy_toSlice, toList_ofList]) hne hd
    · rw [endsWith_bool_eq_getLast?, toList_ofList]
      rcases List.eq_nil_or_concat p with rfl | ⟨q, c, rfl⟩
      · exact absurd rfl hne
      · simp [ws_false (hd c (by simp))]
  · have hp : p = p.dropLast ++ ['\n'] := by
      rcases List.eq_nil_or_concat p with rfl | ⟨q, c, rfl⟩
      · exact absurd rfl hne
      · rw [List.concat_eq_append] at hl ⊢
        rw [List.getLast?_concat, Option.any_some, beq_iff_eq] at hl
        have hc : c = '\n' := Char.toNat_inj.1 (hl.trans rfl)
        simp [hc]
    have hst : (String.ofList p).toSlice.startsWith Char.isWhitespace = false := by
      rw [Slice.startsWith_bool_eq_head?, copy_toSlice, toList_ofList, hp]
      cases hq : p.dropLast with
      | nil => exact absurd hq hne
      | cons c cs => simp [ws_false (hd c (by simp [hq]))]
    rw [Slice.dropWhile_eq_self hst, dropEndWhile_toSlice]
    have hsplit := String.dropEndWhile_append_takeEndWhile (s := String.ofList p)
      (pat := Char.isWhitespace)
    have hT := String.revAll_takeEndWhile (s := String.ofList p) (pat := Char.isWhitespace)
    have hD := String.endsWith_dropEndWhile (s := String.ofList p) (pat := Char.isWhitespace)
    rw [Slice.revAll_bool_eq] at hT
    rw [Slice.endsWith_bool_eq_getLast?] at hD
    have hL := congrArg String.toList hsplit
    rw [String.toList_append, toList_ofList] at hL
    have hDd := split_nl (hL.trans hp) hT hD hd
    have hv : tokV p = decVal p.dropLast := by
      rw [tokV, hp, List.filter_append, List.filter_eq_self.2 (fun c hc => hd c hc)]
      simp
    rw [hv]
    exact slice_toNat? hDd hne hd

theorem filterMap_some_eq {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x (by simp), List.map_cons,
      filterMap_some_eq f g l fun y hy => h y (by simp [hy])]

theorem parseNums_ofList (cs : List Char) (h : (cs.splitOn ' ').all goodK = true) :
    parseNums (String.ofList cs) = ((cs.splitOn ' ').map tokV).toArray := by
  unfold parseNums
  have hsp : (" " : String) = String.singleton ' ' := by
    rw [String.singleton_eq_ofList]
  rw [hsp, splitOn_ofList, List.filterMap_map]
  congr 1
  refine filterMap_some_eq _ _ _ fun p hp => ?_
  exact tok_eq (List.all_eq_true.1 h p hp)

@[expose] noncomputable def tblL : List Nat := (G24T.chars.splitOn ' ').map tokV

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem good_all : (G24T.chars.splitOn ' ').all goodK = true := by decide +kernel

theorem tbl_eq : tbl = tblL.toArray := by
  have h : tbl = parseNums g24Text := rfl
  rw [h, G24T.eq]
  exact parseNums_ofList _ good_all

end CertificateChecks.EvenSporG24
