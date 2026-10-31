
module

public import Certificates.Kernel.Sporadic.Fi22.R3147B7
public import Certificates.Kernel.Sporadic.Fi22.R3147B6
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.S3147Base
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public import CFSG.Certificates.NativeValidSchreier
public import CFSG.Certificates.SchreierChainOrderStabilizers
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.InvariantQuadratic
public import CFSG.Monster.B.Fischer.Fi22FaithfulBase
public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C3147

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

abbrev B7 : Array Nat := #[0, 1, 2, 3, 6, 4, 10]

theorem sOK7 : allN 19 (fun j => Nat.beq (Fi22R7.S j) (Fi22ChT.F j)) = true := by quickRfl
theorem sOK6 : allN 19 (fun j => Nat.beq (Fi22R6.S j) (Fi22ChT.F j)) = true := by quickRfl
theorem baseOK7 : allN 7 (fun t => Nat.beq B7[t]! (pg 12 (mask 12) Fi22R7.BP t)) = true := by
  quickRfl
theorem baseOK6 : allN 6 (fun t => Nat.beq fi22BaseArr[t]! (pg 12 (mask 12) Fi22R6.BP t)) = true := by
  quickRfl
theorem genOK : allN 2 (fun k => Nat.beq (Fi22CGT.F k) (Fi22ChT.F k)) = true := by quickRfl
theorem last7 : Nat.beq (rcnt (Fi22R7.LR 6)) 1 = true := by quickRfl
theorem orbits6 : (List.range 6).map (fun i => rcnt (Fi22R6.LR i)) = [3510, 2816, 567, 720, 8, 2] := by
  decide +kernel

theorem binds7 : Binds 3510 12 Fi22R7.S 19 7 Fi22R7.BP fi22StrongArrs B7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22StrongArrs], fun j hj => ?_, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK7 t ht)⟩
  rw [Fi22X.strong_eq hj, Nat.eq_of_beq_eq_true (allN_spec sOK7 j hj)]

theorem binds6 : Binds 3510 12 Fi22R6.S 19 6 Fi22R6.BP fi22StrongArrs fi22BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22StrongArrs], fun j hj => ?_,
    by simp [fi22BaseArr, fi22ChainBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK6 t ht)⟩
  rw [Fi22X.strong_eq hj, Nat.eq_of_beq_eq_true (allN_spec sOK6 j hj)]

theorem orig_eq : fi22StrongArrs.extract 0 2 = fi22OrigArrs := by
  apply Array.ext
  · simp [fi22StrongArrs, fi22OrigArrs]
  · intro k h1 h2
    have hk : k < 2 := by simpa [fi22OrigArrs] using h2
    rw [Array.getElem_extract]
    simp only [Nat.zero_add, fi22OrigArrs, Array.getElem_ofFn]
    have e := Fi22X.strong_eq (j := k) (by omega)
    rw [getElem!_pos _ k (by simp [fi22StrongArrs]; omega)] at e
    rw [e, Fi22G.gen_eq hk, Nat.eq_of_beq_eq_true (allN_spec genOK k hk)]

theorem words_get {j : Nat} (hj : 2 ≤ j) :
    fi22WordArrs[j]! = (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 19 fi22ChainDerivations)[j]! := by
  by_cases h : j < 19
  · rw [getElem!_pos _ j (by simp [fi22WordArrs, h]),
      getElem!_pos _ j (by simp [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, h])]
    have h2 : ¬ j < 2 := by omega
    simp only [fi22WordArrs, CFSG.Sporadic.Schreier.Co3.Native.wordsArr, Array.getElem_ofFn,
      fi22Derivation, h2, ite_false]
  · rw [getElem!_neg _ j (by simp [fi22WordArrs, h]),
      getElem!_neg _ j (by simp [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, h])]

theorem rawChainOK_arrays {base : Array Nat}
    (h : rawChainOK 3510 (fi22StrongArrs.extract 0 2) fi22StrongArrs base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 19 fi22ChainDerivations) 4 = true) :
    rawChainOK 3510 fi22OrigArrs fi22StrongArrs base fi22WordArrs 4 = true := by
  rw [orig_eq] at h
  unfold rawChainOK at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, ?_⟩, h3⟩, h4⟩, ?_⟩, h6⟩, h7⟩, h8⟩, h9⟩
  · simpa [fi22WordArrs, CFSG.Sporadic.Schreier.Co3.Native.wordsArr] using h2
  · rw [allLt_iff] at h5 ⊢
    intro j hj
    by_cases hjO : j < fi22OrigArrs.size
    · simp [hjO]
    · have hj2 : 2 ≤ j := by
        simp [fi22OrigArrs] at hjO
        omega
      rw [words_get hj2]
      exact h5 j hj

theorem fix_of_base {base : Array Nat} {G : Equiv.Perm (Fin 3510)}
    (hfix : ∀ t < base.size, ∀ h : base[t]! < 3510, G ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩)
    (t : Nat) (ht : t < base.size) (r : Nat) (e : base[t]! = r) (h : r < 3510) :
    G ⟨r, h⟩ = ⟨r, h⟩ := by
  subst e
  exact hfix t ht h

noncomputable def fi22Chain7 : RawSchreierDatum 3510 where
  degree_pos := by decide
  originalCount := 2
  strongCount := 19
  baseCount := 7
  originalCount_le := by decide
  original := Vector.ofFn fun k : Fin 2 => fi22GenPerm k
  strong := Vector.ofFn fun j : Fin 19 => fi22StrongPerm j
  base := #v[0, 1, 2, 3, 6, 4, 10]
  base_distinct := by decide
  derivation j _ := toLetters j.val (fi22Derivation j.val)

theorem chain7_strong_get (j : Fin fi22Chain7.strongCount) :
    fi22Chain7.strong.get j = fi22StrongPerm j := by
  change (Vector.ofFn fun j : Fin 19 => fi22StrongPerm j).get j = fi22StrongPerm j
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem chain7_original_get (k : Fin fi22Chain7.originalCount) :
    fi22Chain7.original.get k = fi22GenPerm k := by
  change (Vector.ofFn fun k : Fin 2 => fi22GenPerm k).get k = fi22GenPerm k
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

end CertificateChecks.KernelSpor.Fi22C3147

end
