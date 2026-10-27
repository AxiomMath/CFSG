
module

public import Certificates.Kernel.Sporadic.Fi24Ext.Data
public import Certificates.Kernel.Sporadic.Fi24Br.Rels
public import Certificates.Kernel.Sporadic.Fi24Fix.DataI
public import Certificates.Kernel.Sporadic.Fi23Br.Seed
public import Certificates.Kernel.Sporadic.Fi24Ext.Digits
public import CFSG.Certificates.Kernel.Spor.Fi24ExtSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixInit
public import CFSG.Certificates.Kernel.Spor.Dec3Sound
public import CFSG.Certificates.Kernel.Spor.BytesFSound
public import CFSG.Sporadic.Fi24.ExtWSpec
public import CFSG.Sporadic.Fi24.SetupBase
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.Fi24Ext.V
import Certificates.Kernel.Sporadic.Fi24Ext.W0
import Certificates.Kernel.Sporadic.Fi24Ext.W1
import Certificates.Kernel.Sporadic.Fi24Ext.W2
import Certificates.Kernel.Sporadic.Fi24Ext.W3
import Certificates.Kernel.Sporadic.Fi24Ext.W4
import Certificates.Kernel.Sporadic.Fi24Ext.W5
import Certificates.Kernel.Sporadic.Fi24Ext.W6
import Certificates.Kernel.Sporadic.Fi24Ext.W7
import Certificates.Kernel.Sporadic.Fi24Ext.W8
import Certificates.Kernel.Sporadic.Fi24Ext.W9
import Certificates.Kernel.Sporadic.Fi24Ext.W10
import Certificates.Kernel.Sporadic.Fi24Ext.W11
import Certificates.Kernel.Sporadic.Fi24Ext.W12
import Certificates.Kernel.Sporadic.Fi24Ext.W13
import Mathlib.Tactic.IntervalCases
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.Kernel.Fam.Act
public import CFSG.Certificates.Kernel.LceSP.Cosets
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Fi24.CertificateBase
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CertificateChecks.KernelFi24Ext

open CFSG.KC.Ord CFSG.KS.Mat3 CFSG.KD.Fi24Ext CFSG.KC.Fi24Ext CFSG.KC.Fi24ExtS
  CFSG.Sporadic.Fi24.Native CertificateChecks.KernelSpor.Fi24Rels

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Mt (X : ℕ) : Matrix (Fin 781) (Fin 781) (ZMod 3) := mat3 781 609961 X

abbrev Cn (X : ℕ) : Prop := Canon3 609961 X

theorem mul_mt {X Y : ℕ} (hX : Cn X) (hY : Cn Y) :
    Cn (CFSG.KD.BrFi24.MUL X Y) ∧ Mt (CFSG.KD.BrFi24.MUL X Y) = Mt X * Mt Y :=
  hs.mul_sound X Y hX hY

theorem cn_one : Cn CFSG.KD.BrFi24.ONE := hs.one_q

theorem mt_one : Mt CFSG.KD.BrFi24.ONE = 1 := hs.one_mt

#kc_forall_chunks vld_all (fun k => CFSG.KD.BrFi24.VLD (MX k) = true) 94 CFSG.KD.Fi24Ext.vld 1

theorem vld_ok : ∀ k < 94, CFSG.KD.BrFi24.VLD (MX k) = true := vld_all

theorem cn_MX {k : ℕ} (hk : k < 94) : Cn (MX k) := hs.vld_q _ (vld_ok k hk)

theorem cn_A : Cn (CFSG.KD.BrFi24.RB 23) := hs.vld_q _ vldA

theorem cn_B : Cn (CFSG.KD.BrFi24.RB 24) := hs.vld_q _ vldB

theorem cn_Rt : Cn CFSG.KD.Fi24Fix.R := hs.vld_q _ vldRt

theorem reg_A : REG 0 = CFSG.KD.BrFi24.RB 23 := rfl

theorem reg_B : REG 1 = CFSG.KD.BrFi24.RB 24 := rfl

theorem reg_B2 : REG 2 = B2 := rfl

theorem reg_G {j : ℕ} (hj : j < 13) : REG (3 + j) = G j := by
  interval_cases j <;> rfl

theorem reg_Gi {j : ℕ} (hj : j < 13) : REG (16 + j) = Gi j := by
  interval_cases j <;> rfl

theorem cn_G {j : ℕ} (hj : j < 13) : Cn (G j) := cn_MX (by omega)

theorem cn_Gi {j : ℕ} (hj : j < 13) : Cn (Gi j) := cn_MX (k := 13 + j) (by omega)

theorem cn_reg {r : ℕ} (hr : r < 29) : Cn (REG r) := by
  rcases Nat.lt_or_ge r 3 with h | h
  · interval_cases r
    · exact cn_A
    · exact cn_B
    · exact cn_MX (k := 26) (by norm_num)
  · rcases Nat.lt_or_ge r 16 with h' | h'
    · have e := reg_G (j := r - 3) (by omega)
      rw [show 3 + (r - 3) = r by omega] at e
      rw [e]
      exact cn_G (by omega)
    · have e := reg_Gi (j := r - 16) (by omega)
      rw [show 16 + (r - 16) = r by omega] at e
      rw [e]
      exact cn_Gi (by omega)

theorem wordMul_mt {Y : ℕ} (hY : Cn Y) : ∀ w : List ℕ, (∀ r ∈ w, r < 29) →
    Cn (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG w Y) ∧
      Mt (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG w Y) =
        (w.map fun r => Mt (REG r)).prod * Mt Y
  | [], _ => ⟨hY, by simp [CFSG.KC.Fi24Fix.wordMul]⟩
  | r :: w, hw => by
    obtain ⟨h1, h2⟩ := wordMul_mt hY w (fun r' hr' => hw r' (List.mem_cons_of_mem r hr'))
    have e : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (r :: w) Y =
        CFSG.KD.BrFi24.MUL (REG r) (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG w Y) := rfl
    obtain ⟨h3, h4⟩ := mul_mt (cn_reg (hw r List.mem_cons_self)) h1
    rw [e]
    refine ⟨h3, ?_⟩
    rw [h4, h2, List.map_cons, List.prod_cons, Matrix.mul_assoc]

#kc_forall_chunks chunks_all (fun g => Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC g)
  (chunkIn FS CFSG.KD.Fi24Ext.ST CFSG.KD.BrFi24.ONE g)) (CFSG.KD.Fi24Ext.ST g) = true) 55 CFSG.KD.Fi24Ext.c 1

theorem chunks_ok : ∀ g < 55, Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL REG (WC g)
    (chunkIn FS CFSG.KD.Fi24Ext.ST CFSG.KD.BrFi24.ONE g)) (CFSG.KD.Fi24Ext.ST g) = true :=
  chunks_all

theorem chunkIn_first {g : ℕ} (h : FS g = true) :
    chunkIn FS CFSG.KD.Fi24Ext.ST CFSG.KD.BrFi24.ONE g = CFSG.KD.BrFi24.ONE := by
  unfold chunkIn
  rw [h]

theorem chunkIn_next {g : ℕ} (h : FS g = false) :
    chunkIn FS CFSG.KD.Fi24Ext.ST CFSG.KD.BrFi24.ONE g = CFSG.KD.Fi24Ext.ST (g - 1) := by
  unfold chunkIn
  rw [h]
  rfl

theorem words_data : ∀ w < 19, 0 < MJ.getD w 0 ∧ OJ.getD w 0 + MJ.getD w 0 ≤ 55 ∧
    FS (OJ.getD w 0) = true ∧ (∀ t < MJ.getD w 0, 0 < t → FS (OJ.getD w 0 + t) = false) ∧
    ((List.range (MJ.getD w 0)).reverse.flatMap fun t => WC (OJ.getD w 0 + t)) = WL w := by
  decide +kernel

theorem wc_lt : ∀ g < 55, ∀ r ∈ WC g, r < 29 := by decide +kernel

theorem flat_succ (o t : ℕ) : ((List.range (t + 2)).reverse.flatMap fun s => WC (o + s)) =
    WC (o + (t + 1)) ++ ((List.range (t + 1)).reverse.flatMap fun s => WC (o + s)) := by
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatMap_cons]

theorem word_mt {w : ℕ} (hw : w < 19) :
    Cn (CFSG.KD.Fi24Ext.ST (OJ.getD w 0 + MJ.getD w 0 - 1)) ∧
      Mt (CFSG.KD.Fi24Ext.ST (OJ.getD w 0 + MJ.getD w 0 - 1)) = ((WL w).map fun r => Mt (REG r)).prod := by
  obtain ⟨hm, hle, hfs, hfs', hflat⟩ := words_data w hw
  set o := OJ.getD w 0
  set m := MJ.getD w 0
  have key : ∀ t < m, Cn (CFSG.KD.Fi24Ext.ST (o + t)) ∧ Mt (CFSG.KD.Fi24Ext.ST (o + t)) =
      (((List.range (t + 1)).reverse.flatMap fun s => WC (o + s)).map fun r => Mt (REG r)).prod := by
    intro t ht
    induction t with
    | zero =>
      have hc := Nat.eq_of_beq_eq_true (chunks_ok o (by omega))
      rw [chunkIn_first hfs] at hc
      obtain ⟨h1, h2⟩ := wordMul_mt cn_one (WC o) (wc_lt o (by omega))
      rw [hc] at h1 h2
      rw [Nat.add_zero]
      refine ⟨h1, ?_⟩
      rw [h2, mt_one, Matrix.mul_one]
      simp
    | succ t ih =>
      obtain ⟨i1, i2⟩ := ih (by omega)
      have hc := Nat.eq_of_beq_eq_true (chunks_ok (o + (t + 1)) (by omega))
      rw [chunkIn_next (hfs' (t + 1) ht (by omega)), show o + (t + 1) - 1 = o + t by omega] at hc
      obtain ⟨h1, h2⟩ := wordMul_mt i1 (WC (o + (t + 1))) (wc_lt _ (by omega))
      rw [hc] at h1 h2
      refine ⟨h1, ?_⟩
      rw [h2, i2, flat_succ, List.map_append, List.prod_append]
  have := key (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega, hflat] at this
  rwa [show o + (m - 1) = o + m - 1 by omega] at this

theorem st_G : ∀ j < 13, CFSG.KD.Fi24Ext.ST (OJ.getD j 0 + MJ.getD j 0 - 1) = G j := by
  intro j hj
  interval_cases j <;> rfl

theorem st_W0 : CFSG.KD.Fi24Ext.ST (OJ.getD 13 0 + MJ.getD 13 0 - 1) = W0 := rfl
theorem st_W1 : CFSG.KD.Fi24Ext.ST (OJ.getD 14 0 + MJ.getD 14 0 - 1) = W1 := rfl
theorem st_U : CFSG.KD.Fi24Ext.ST (OJ.getD 15 0 + MJ.getD 15 0 - 1) = U := rfl
theorem st_Xw : CFSG.KD.Fi24Ext.ST (OJ.getD 16 0 + MJ.getD 16 0 - 1) = Xw := rfl
theorem st_Yw : CFSG.KD.Fi24Ext.ST (OJ.getD 17 0 + MJ.getD 17 0 - 1) = Yw := rfl
theorem st_X2w : CFSG.KD.Fi24Ext.ST (OJ.getD 18 0 + MJ.getD 18 0 - 1) = X2w := rfl

end CertificateChecks.KernelFi24Ext

end
