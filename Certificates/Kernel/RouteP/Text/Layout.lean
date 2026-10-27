module

public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Certificates.Kernel.RouteP.TextSplit
public import Certificates.Kernel.RouteP.Text.Texts
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KS.RouteP CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem allIn_zero_eq (n : Nat) (p : Nat → Bool) :
    CFSG.Sporadic.Th.Native.allIn 0 n p = (List.range n).all p := by
  apply Bool.eq_iff_iff.mpr
  rw [CFSG.Sporadic.Th.allIn_eq_true, List.all_eq_true]
  simp

theorem array_range_eq (n : Nat) : Array.range n = (List.range n).toArray := by
  apply Array.toList_inj.mp
  rw [Array.toList_range, List.toList_toArray]

theorem lineNums_lit {s : String} {cs : List Char} (e : s = String.ofList cs) (pre : String)
    (p : List Char) (hp : pre.toList = p) (skip : Nat) (h : lineNumsOKL p skip cs = true) :
    lineNums s pre skip = (lineNumsL p skip cs).toArray := by
  rw [e, lineNums_ofList pre skip cs (hp ▸ h), hp]

theorem ok_y332_out :
    lineNumsOKL ['O', 'U', 'T', ' ', 'Y', '3', '3', '2', ' '] 2 TY332.chars = true := by
  decide +kernel

theorem ok_y332_chain : lineNumsOKL ['C', 'H', 'A', 'I', 'N', ' ', 'Y', '3', '3', '2', ' ',
    'O', 'R', 'D', 'E', 'R', ' '] 3 TY332.chars = true := by
  decide +kernel

theorem ok_y332_level : levelOKL ['L', 'E', 'V', 'E', 'L', ' '] TY332.chars = true := by
  decide +kernel

theorem y332DataOK_true : y332DataOK () = true := by
  unfold y332DataOK
  have hl : "LEVEL ".toList = ['L', 'E', 'V', 'E', 'L', ' '] := rfl
  rw [y332Lines_eq, lineNums_lit TY332.eq "OUT Y332 " ['O', 'U', 'T', ' ', 'Y', '3', '3', '2', ' '] rfl 2
      ok_y332_out,
    lineNums_lit TY332.eq "CHAIN Y332 ORDER " ['C', 'H', 'A', 'I', 'N', ' ', 'Y', '3', '3', '2', ' ',
      'O', 'R', 'D', 'E', 'R', ' '] rfl 3 ok_y332_chain, TY332.eq,
    y332LevelNums_ofList _ (hl ▸ ok_y332_level), hl]
  simp only [allIn_zero_eq, array_range_eq]
  decide +kernel

theorem lineNums_of {s : String} {cs : List Char} (e : s = String.ofList cs) (pre : String)
    (skip : Nat) (h : lineNumsOKL pre.toList skip cs = true) :
    lineNums s pre skip = (lineNumsL pre.toList skip cs).toArray := by
  rw [e, lineNums_ofList pre skip cs h]

theorem invArr_eq (p : Array Nat) : invArr p =
    (List.range' 0 p.size).foldl (fun r i => r.set! p[i]! i) (Array.replicate p.size 0) := by
  simp only [invArr, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size]
  simp
  rfl

theorem getElem!_one_map (L : List (List Char)) :
    (L.map String.ofList)[1]! = String.ofList (L.getD 1 []) := by
  match L with
  | [] => rfl
  | [_] => rfl
  | _ :: b :: _ => rfl

@[expose] def coverSep : List Char := ['\n', '[', 'c', 'o', 'v', 'e', 'r', ']']

@[expose] noncomputable def baseCoverK : List Char := (splitSepL TBase.chars coverSep).getD 1 []

theorem ascii_of_all {cs : List Char} (h : cs.all (fun c => decide (c.toNat < 128)) = true) :
    ∀ c ∈ cs, c.toNat < 128 := by
  simpa using h

theorem baseSplit : (baseText.splitOn "\n[cover]")[1]! = String.ofList baseCoverK := by
  have e : ("\n[cover]" : String) = String.ofList coverSep := by
    rw [← String.toList_inj, String.toList_ofList]
    decide +kernel
  rw [TBase.eq, e, splitOn_ofList_sep (ascii_of_all (by decide +kernel)) (ascii_of_all (by decide +kernel))
    (by decide),
    getElem!_one_map]
  rfl

theorem ok_h0 : lineNumsOKL "OUT H0 ".toList 2 TStab.chars = true := by decide +kernel
theorem ok_eps : lineNumsOKL "OUT EPS ".toList 2 TN0.chars = true := by decide +kernel
theorem ok_ab : lineNumsOKL "OUT M24AB ".toList 2 TN0.chars = true := by decide +kernel
theorem ok_orb : lineNumsOKL "EPSORBIT ".toList 1 TN0.chars = true := by decide +kernel
theorem ok_pa : lineNumsOKL "PLANEPERM a ".toList 2 TN0.chars = true := by decide +kernel
theorem ok_pb : lineNumsOKL "PLANEPERM b ".toList 2 TN0.chars = true := by decide +kernel
theorem ok_plane : lineNumsOKL "plane ".toList 2 baseCoverK = true := by decide +kernel

theorem dataOK_true : dataOK () = true := by
  unfold dataOK
  rw [objLines_eq, lineNums_of TStab.eq _ _ ok_h0, lineNums_of TN0.eq _ _ ok_eps,
    lineNums_of TN0.eq _ _ ok_ab, lineNums_of TN0.eq _ _ ok_orb, lineNums_of TN0.eq _ _ ok_pa,
    lineNums_of TN0.eq _ _ ok_pb, baseSplit, lineNums_of rfl _ _ ok_plane, invArr_eq, invArr_eq]
  decide +kernel

end CertificateChecks.KernelRouteP

