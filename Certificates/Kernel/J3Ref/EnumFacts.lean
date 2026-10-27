module

public import Certificates.Kernel.J3Ref.Faith
public import Certificates.Kernel.J3Ref.Small
public import Certificates.Kernel.J3Ref.RecC
public import Certificates.Kernel.J3Ref.RecM
public import Certificates.Kernel.J3Ref.RecN
public import Certificates.Kernel.Sporadic.OddCore.J3FourGen
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Spor.JoinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3Ref

open CFSG.SectionRank.QTK.Insp443.J3Cls CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.KS.PEnumB CFSG.KS.Join CertificateChecks.KernelSpor

#kc_forall_chunks hvS_all (fun k => hvS k = true) 128 CertificateChecks.KernelJ3Ref.hvS 1
#kc_forall_chunks sCl_all (fun k => sCl k = true) 3 CertificateChecks.KernelJ3Ref.sCl 1
#kc_forall_chunks cPt_all (fun k => cPt k = true) 30 CertificateChecks.KernelJ3Ref.cPt 1
#kc_forall_chunks hvC_all (fun k => hvC k = true) 1920 CertificateChecks.KernelJ3Ref.hvC 1
#kc_forall_chunks cHS_all (fun k => cHS k = true) 30 CertificateChecks.KernelJ3Ref.cHS 1
#kc_forall_chunks cCl_all (fun k => cCl k = true) 30 CertificateChecks.KernelJ3Ref.cCl 1
#kc_forall_chunks mPt_all (fun k => mPt k = true) 15 CertificateChecks.KernelJ3Ref.mPt 1
#kc_forall_chunks hvM_all (fun k => hvM k = true) 960 CertificateChecks.KernelJ3Ref.hvM 1
#kc_forall_chunks mHS_all (fun k => mHS k = true) 15 CertificateChecks.KernelJ3Ref.mHS 1
#kc_forall_chunks mCl_all (fun k => mCl k = true) 6 CertificateChecks.KernelJ3Ref.mCl 1
#kc_forall_chunks mNp_all (fun k => mNp k = true) 3 CertificateChecks.KernelJ3Ref.mNp 1
#kc_forall_chunks nPt_all (fun k => nPt k = true) 45 CertificateChecks.KernelJ3Ref.nPt 1
#kc_forall_chunks hvN_all (fun k => hvN k = true) 2880 CertificateChecks.KernelJ3Ref.hvN 1
#kc_forall_chunks nHS_all (fun k => nHS k = true) 45 CertificateChecks.KernelJ3Ref.nHS 1
#kc_forall_chunks nCl_all (fun k => nCl k = true) 27 CertificateChecks.KernelJ3Ref.nCl 1

theorem blocks_spec {f : Nat → Bool} {B N : Nat} (h : ∀ b < N, allBlk (Nat.mul b B) f B = true) :
    ∀ i < N * B, f i = true := by
  intro i hi
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0
      simp at hi
    · exact h0
  have hb : i / B < N := (Nat.div_lt_iff_lt_mul hB).2 hi
  have := allBlk_spec (h _ hb) (i % B) (Nat.mod_lt i hB)
  rwa [show Nat.add (Nat.mul (i / B) B) (i % B) = i by
    simp only [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod' i B] at this

theorem bounded_spec {f : Nat → Bool} {B N bound : Nat} (hN : bound ≤ N * B)
    (h : ∀ b < N, allBlk (Nat.mul b B) (fun c => bIf(Nat.blt c bound, f c, true)) B = true) :
    ∀ c < bound, f c = true := by
  intro c hc
  have := blocks_spec h c (by omega)
  have e : Nat.blt c bound = true := Nat.blt_eq.mpr hc
  simpa [CFSG.KS.Raw.Orb.bIf_eq, e] using this

theorem clsTbl_tab {k : Nat} (hk : k < 10) : clsTbl k = tabT (unpack 6156 13 (J3ClsP k)) := by
  have h := hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 10) ClsT.all cls_join
    (by norm_num) k hk
  rw [← ClsT.eq] at h
  rw [← tabT_natArr (clsTbl k)]
  exact congrArg tabT h

theorem tbOK_all : ∀ i < 16, tbOK i = true := by
  intro i hi
  rcases Nat.lt_or_ge i 8 with h | h
  · simpa using allBlk_spec tbls_ok0 i h
  · have := allBlk_spec tbls_ok1 (i - 8) (by omega)
    rwa [show Nat.add 8 (i - 8) = i by simp only [Nat.add_eq]; omega] at this

theorem tb_facts {i : Nat} (hi : i < 16) :
    canonK 6156 13 (mask 13) (6156 * 13) (tbP i) = true ∧
      canonK 6156 13 (mask 13) (6156 * 13) (tbI i) = true ∧
      invEqK 6156 13 (mask 13) (6156 * 13) (tbP i) (tbI i) = true := by
  have h := tbOK_all i hi
  unfold tbOK at h
  simpa only [bAnd_iff] using h

theorem wordOK_all : ∀ i < 16, wordOK i = true := by
  intro i hi
  rcases Nat.lt_or_ge i 4 with h0 | h0
  · simpa using allBlk_spec words0 i h0
  rcases Nat.lt_or_ge i 8 with h1 | h1
  · have := allBlk_spec words1 (i - 4) (by omega)
    rwa [show Nat.add 4 (i - 4) = i by simp only [Nat.add_eq]; omega] at this
  rcases Nat.lt_or_ge i 12 with h2 | h2
  · have := allBlk_spec words2 (i - 8) (by omega)
    rwa [show Nat.add 8 (i - 8) = i by simp only [Nat.add_eq]; omega] at this
  · have := allBlk_spec words3 (i - 12) (by omega)
    rwa [show Nat.add 12 (i - 12) = i by simp only [Nat.add_eq]; omega] at this

theorem mj_tbP {i : Nat} (hi : i < 16) : MJ (tbP i) :=
  mj_of_word (tb_facts hi).1 (wordOK_all i hi)

theorem mj_tbI {i : Nat} (hi : i < 16) : MJ (tbI i) :=
  mj_inv (mj_tbP hi) (tb_facts hi).2.1 (tb_facts hi).2.2

theorem enum_of {k cnt m : Nat} {G GI GJ T PL POS SRT SRI HS HSI HV CL : Nat → Nat}
    {gs : List Table} (hg : TabsOK 6156 13 k GI gs.toArray) (hG : ∀ j < k, G j = pidn 6156 13)
    (hGI : ∀ j < k, MJ (GI j)) (hGJ : ∀ j < k, MJ (GJ j))
    (hgj : ∀ j < k, invEqK 6156 13 (mask 13) (6156 * 13) (GI j) (GJ j) = true)
    (hh : penumHdK (pidn 6156 13) cnt 3000 T PL = true)
    (hb : ∀ i < cnt, penumPtB 6156 13 (mask 13) bsJ GI k cnt T PL POS SRT SRI i = true)
    (hv : ∀ i < cnt, hvK 6156 13 (mask 13) T HV i = true)
    (hs : ∀ i < cnt, hsortVK cnt HV HS HSI i = true)
    (hc : ∀ c < cnt * (k + k), findProdB cnt 13 (mask 13) bsJ (k + k) T (bothK k GI GJ) CL c = true)
    (hm : cnt = m) :
    enumOK 6156 3000 m gs = true ∧ mulClosureH 6156 gs.toArray 3000 = hRec 6156 13 cnt T PL ∧
      ∀ i < cnt, MJ (T i) := by
  have hT := penumB_mem mj_faith hGI hh hb
  have hp := penumPtK_of_B (G := G) mj_faith hGI hG hh hb
  have hs' := hsortPtK_of_V hv hs
  have hS : ∀ j < k + k, MJ (bothK k GI GJ j) := fun j hj => by
    rcases Nat.lt_or_ge j k with h | h
    · rw [bothK_lt h]
      exact hGI j h
    · rw [bothK_ge h]
      exact hGJ _ (by omega)
  refine ⟨enumOK_of szOK_j3 hG hg (fun j hj => ⟨hgj j hj, (hGJ j hj).1⟩) hh hp hs'
    (fun c hc' => findPtK_prod_of_B mj_faith hT hS hc' (hc c hc')) hm,
    (mulH_sound szOK_j3 hG hg hh hp hs').1, hT⟩

end CertificateChecks.KernelJ3Ref

end
