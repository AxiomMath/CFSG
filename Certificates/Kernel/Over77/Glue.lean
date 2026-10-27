module

public import Certificates.Kernel.Over77.Data
public import Certificates.Data.Kernel.Over77.Bridge
public import CFSG.Certificates.Kernel.Over77Sound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Data
import Certificates.Kernel.Over77.Mul0
import Certificates.Kernel.Over77.Mul1
import Certificates.Kernel.Over77.Mul2
import Certificates.Kernel.Over77.Mul3
import Certificates.Kernel.Over77.Cls
import Certificates.Kernel.Over77.Small
import Certificates.Kernel.Over77.Bridge
import CFSG.Certificates.Kernel.Common.RowsForall
import CFSG.Certificates.Kernel.Common.Repo
public import Mathlib.GroupTheory.Perm.Basic

#kc_repo #kc_rows_forall CFSG.KD.Over77.c12630mulA (fun i D => CFSG.KD.Over77.mulR i D)
  "Certificates/Kernel/Over77/data/mul.txt.gz" 442046 18050228659166210537 0 252
  CFSG.KD.Over77.c12630mul

#kc_repo #kc_rows_forall CFSG.KD.Over77.c12630mulB (fun i D => CFSG.KD.Over77.mulR i D)
  "Certificates/Kernel/Over77/data/mul.txt.gz" 442046 18050228659166210537 252 504
  CFSG.KD.Over77.c12630mul

#kc_repo #kc_rows_forall CFSG.KD.Over77.c12630mulC (fun i D => CFSG.KD.Over77.mulR i D)
  "Certificates/Kernel/Over77/data/mul.txt.gz" 442046 18050228659166210537 504 756
  CFSG.KD.Over77.c12630mul

#kc_repo #kc_rows_forall CFSG.KD.Over77.c12630mulD (fun i D => CFSG.KD.Over77.mulR i D)
  "Certificates/Kernel/Over77/data/mul.txt.gz" 442046 18050228659166210537 756 1008
  CFSG.KD.Over77.c12630mul

#kc_repo #kc_rows_forall CFSG.KD.Over77.c12630clsAll (fun i D => CFSG.KD.Over77.clsR i D)
  "Certificates/Kernel/Over77/data/cls.txt.gz" 52120 3933342631937138028 0 252
  CFSG.KD.Over77.c12630cls

#kc_repo #kc_rows_forall CFSG.KD.Over77.c12630pwAll (fun p len W => CFSG.KD.Over77.pwR p len W)
  "Certificates/Kernel/Over77/data/pw.txt.gz" 1045 6243921055104446018 0 110
  CFSG.KD.Over77.c12630pw

#kc_repo #kc_rows_forall CFSG.KD.Over77.c12630swAll (fun i len W => CFSG.KD.Over77.swR i len W)
  "Certificates/Kernel/Over77/data/sw.txt.gz" 1109 10199449385633197420 0 82
  CFSG.KD.Over77.c12630sw

public section

namespace CFSG.KD.Over77

open CFSG.KC.Over77 CFSG.KC.Enum CFSG.KS CFSG.KS.Over77
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 (dataA dataB dataZ dataSigma dataS idA)

theorem bridgeK_spec {a : Nat} {d : Array Nat} (h : bridgeK a d = true) :
    ∀ i < 77, pg 7 (mask 7) a i = d.getD i 0 := fun i hi =>
  Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem c12630_over77 (pA pB pZ σ : Equiv.Perm (Fin 77)) (s : Fin 9 → Equiv.Perm (Fin 77))
    (hA : Array.ofFn (fun i => (pA i : Nat)) = dataA)
    (hB : Array.ofFn (fun i => (pB i : Nat)) = dataB)
    (hZ : Array.ofFn (fun i => (pZ i : Nat)) = dataZ)
    (hσ : Array.ofFn (fun i => (σ i : Nat)) = dataSigma)
    (hs : ∀ k : Fin 9, Array.ofFn (fun i => (s k i : Nat)) = dataS.getD k idA)
    (L : Subgroup (Equiv.Perm (Fin 77))) (hPL : Subgroup.closure {pA, pB, pZ} ≤ L)
    (hL : L ≤ Subgroup.closure (Set.range s))
    (hnot : ¬ L ≤ Subgroup.closure {pA, pB, pZ}) : σ ∈ L := by
  have hb := c12630bridge
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨hbA, hbB⟩, hbZ⟩, hbσ⟩, hbS⟩ := hb
  have hmul : ∀ i < 1008, ∃ D, mulK T P (nth S) i D = true := by
    intro i hi
    by_cases h1 : i < 252
    · exact c12630mulA i (Nat.zero_le _) h1
    by_cases h2 : i < 504
    · exact c12630mulB i (Nat.le_of_not_lt h1) h2
    by_cases h3 : i < 756
    · exact c12630mulC i (Nat.le_of_not_lt h2) h3
    · exact c12630mulD i (Nat.le_of_not_lt h3) hi
  exact over77_sound (T := T) (P := P) (X := X) (S := nth S) c12630t0 hmul
    (fun i hi => c12630clsAll i (Nat.zero_le _) hi)
    (fun p hp => c12630pwAll p (Nat.zero_le _) hp)
    (fun i hi => c12630swAll i (Nat.zero_le _) hi)
    (fr_of_ofFn hA (bridgeK_spec hbA)) (fr_of_ofFn hB (bridgeK_spec hbB))
    (fr_of_ofFn hZ (bridgeK_spec hbZ)) (fr_of_ofFn hσ (bridgeK_spec hbσ))
    (fun k => fr_of_ofFn (hs k) (bridgeK_spec (allN_spec hbS k.val k.2))) L hPL hL hnot

end CFSG.KD.Over77

end
