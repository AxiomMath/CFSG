module

public import Certificates.Kernel.HSStd.U43VaChecks
public import Certificates.Kernel.Sporadic.OddCore.U43CoverKF
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.MulHFSound
import CFSG.Certificates.Kernel.Spor.PEnumRCSound
import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import Certificates.Kernel.Sporadic.OddCore.CentGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Va

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelHSStd
open CertificateChecks.KernelSpor (U43CoverK.inP_tab U43CoverK.gen_of U43CoverK.tP)

#kc_forall_chunks pe_all (fun s => pe s = true) 30 CertificateChecks.KernelHSStd.U43Va.pe 1
#kc_forall_chunks hs_all (fun s => hs s = true) 10 CertificateChecks.KernelHSStd.U43Va.hs 1

theorem sz : szOK 820 10 = true := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem vaCg_size : vaCg.size = 5 := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem inF {i : Nat} (hi : i < 9) : cK (U43VP i) = true ∧ cK (U43VI i) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (U43VP i) (U43VI i) = true := by
  have h := allN_spec kIn i hi
  simp only [bAnd_iff] at h
  exact h

theorem tkF {k : Nat} (hk : k < 8) : cK (TK k) = true ∧
    permOK 820 10 (mask 10) (820 * 10) (TK k) (TKI k) = true := by
  have h := allN_spec kTK k hk
  simp only [bAnd_iff] at h
  exact h

theorem ppow_eq {p : Nat} (hp : cK p = true) : ∀ e,
    powA 820 (unpack 820 10 p) e = unpack 820 10 (ppow p e) ∧ cK (ppow p e) = true
  | 0 => ⟨idA_eq sz, (PP.id sz).1⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := ppow_eq hp e
    change compA 820 (unpack 820 10 p) (powA 820 (unpack 820 10 p) e) =
      unpack 820 10 (pc p (ppow p e)) ∧ cK (pc p (ppow p e)) = true
    rw [h1, compA_unpack hp h2]
    exact ⟨rfl, canonK_pcomp hp h2⟩

theorem phi_eq : phiArr = unpack 820 10 (U43VP 7) := eq_unpack_of_bindListK kBind.2.2.2.2.2.2.2.1

theorem delta_eq : deltaArr = unpack 820 10 (U43VP 8) := eq_unpack_of_bindListK kBind.2.2.2.2.2.2.2.2

theorem tArr_eq (k : Nat) : tArr k = unpack 820 10 (TK k) := by
  obtain ⟨a1, a2⟩ := ppow_eq (inF (i := 7) (by decide)).1 (k / 4)
  obtain ⟨b1, b2⟩ := ppow_eq (inF (i := 8) (by decide)).1 (k % 4)
  unfold tArr TK
  rw [phi_eq, delta_eq, a1, b1, compA_unpack a2 b2]
  rfl

theorem memCos_of {i : Nat} (h1 : 1 ≤ i) (h6 : i ≤ 6) :
    memCos [0, 2, 4, 6] (tabT (unpack 820 10 (U43VP i))) = true := by
  have hc := allN_spec kCos (i - 1) (by omega)
  rw [show Nat.succ (i - 1) = i by omega] at hc
  unfold cosK at hc
  rw [CFSG.KC.BfsPin.strictB_app] at hc
  simp only [bAnd_iff] at hc
  obtain ⟨hk8, hk2, hs⟩ := hc
  have hk8' := Nat.blt_eq.mp hk8
  have hk2' : U43VC i % 2 = 0 := Nat.eq_of_beq_eq_true hk2
  obtain ⟨tc, tp⟩ := tkF hk8'
  have hpp := PP_of_permOK sz tp
  have hx := (inF (i := i) (by omega)).1
  have hxi : cK (pc (U43VP i) (TKI (U43VC i))) = true := canonK_pcomp hx hpp.inv.1
  unfold memCos
  rw [List.any_eq_true]
  refine ⟨U43VC i, by simp only [List.mem_cons, List.not_mem_nil]; omega, ?_⟩
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hk8', ?_⟩
  rw [natArr_tabT hx, tArr_eq, invCand_unpack tp, compA_unpack hx hpp.inv.1]
  have := U43CoverK.inP_tab hxi hs
  unfold U43CoverK.tP at this
  rwa [natArr_tabT hxi] at this

theorem gen_tabs : TabsOK 820 10 5 U43VA.GI (tabsOf vaCg) := by
  have hh := kHead
  simp only [bAnd_iff] at hh
  refine ⟨by simp [tabsOf, vaCg_size], fun j hj => ?_⟩
  have hm : (tabsOf vaCg)[j]! = tabOf vaCg[j]! := by
    have hj' : j < vaCg.size := by rw [vaCg_size]; exact hj
    unfold tabsOf
    rw [getElem!_pos _ j (by simpa using hj'), Array.getElem_map, getElem!_pos vaCg j hj']
  have h := allN_spec hh.1 j hj
  simp only [bAnd_iff] at h
  rw [Nat.eq_of_beq_eq_true h.1]
  have hb : vaCg[j]! = unpack 820 10 (U43VP (j + 2)) := by
    have hk := kBind
    obtain ⟨-, -, b0, b1, b2, b3, b4, -, -⟩ := hk
    match j, hj with
    | 0, _ => exact eq_unpack_of_bindListK b0
    | 1, _ => exact eq_unpack_of_bindListK b1
    | 2, _ => exact eq_unpack_of_bindListK b2
    | 3, _ => exact eq_unpack_of_bindListK b3
    | 4, _ => exact eq_unpack_of_bindListK b4
  refine ⟨?_, (inF (i := j + 2) (by omega)).1⟩
  rw [hm, hb]
  rfl

theorem rep8_eq : (tabOf reps[8]!) = tabT (unpack 820 10 (U43VP 0)) := by
  have : reps[8]! = rep8 := rfl
  rw [this, eq_unpack_of_bindListK kBind.1]
  rfl

theorem vaZ_eq : tabOf vaZ = tabT (unpack 820 10 (U43VP 1)) := by
  rw [eq_unpack_of_bindListK kBind.2.1]
  rfl

theorem pa : ∀ s < 30, pe s = true := pe_all
theorem ha : ∀ s < 10, hs s = true := hs_all

theorem mulRecArr_unpack {k : Nat} {GI T : Nat → Nat} {A : Array Table} {par : Array (ℕ × ℕ)}
    (hA : TabsOK 820 10 k GI A) (h0 : idT 820 = tabT (unpack 820 10 (T 0)))
    (hT : ∀ i < par.size + 1, cK (T i) = true)
    (hpar : ∀ i < par.size, par[i]!.1 ≤ i ∧ par[i]!.2 < k ∧
      T (i + 1) = pc (T par[i]!.1) (GI par[i]!.2)) :
    mulRecArr A par = Array.ofFn (n := par.size + 1) fun i => tabT (unpack 820 10 (T i.val)) := by
  have key : (mulRecArr A par).size = par.size + 1 ∧
      ∀ j < par.size + 1, (mulRecArr A par)[j]! = tabT (unpack 820 10 (T j)) := by
    unfold mulRecArr
    refine Array.foldl_induction (motive := fun (i : ℕ) (a : Array Table) => a.size = i + 1 ∧
      ∀ j < i + 1, a[j]! = tabT (unpack 820 10 (T j))) ?_ ?_
    · refine ⟨rfl, fun j hj => ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0
      exact h0
    · rintro ⟨i, hi⟩ b ⟨hsz, hb⟩
      change b.size = i + 1 at hsz
      change ∀ j < i + 1, b[j]! = tabT (unpack 820 10 (T j)) at hb
      have hp := hpar i hi
      rw [getElem!_pos par i hi] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      simp only [Fin.getElem_fin]
      refine ⟨by rw [Array.size_push, hsz], fun j hj => ?_⟩
      by_cases hji : j < b.size
      · rw [getElem!_pos _ j (by rw [Array.size_push]; omega), Array.getElem_push_lt hji,
          ← getElem!_pos b j hji]
        exact hb j (by omega)
      · have hj' : j = b.size := by omega
        subst hj'
        rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq, hsz,
          hb _ (by omega), (hA.2 _ h2).1, h3]
        exact compT_unpack (hT _ (by omega)) (hA.2 _ h2).2
  refine Array.ext (by rw [key.1, Array.size_ofFn]) fun j h1 h2 => ?_
  rw [← getElem!_pos _ j h1, key.2 j (by rw [key.1] at h1; exact h1), Array.getElem_ofFn]

theorem enum_ok :
    enumRecOK (tabsOf vaCg) (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL) 2880 = true := by
  have hh := kHead
  simp only [bAnd_iff] at hh
  obtain ⟨hg, hcnt, -, hhd⟩ := hh
  have hcnt' : U43VA.cnt = 2880 := Nat.eq_of_beq_eq_true hcnt
  have hinv : ∀ j < 5, invEqK 820 10 (mask 10) (820 * 10) (U43VA.GI j) (GJ j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (GJ j) = true := fun j hj => by
    have h := allN_spec hg j hj
    simp only [bAnd_iff] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    exact ⟨(inF (i := j + 2) (by omega)).2.2, (inF (i := j + 2) (by omega)).2.1⟩
  have hh2 := hhd
  unfold penumHdK at hh2
  simp only [bAnd_iff] at hh2
  have hT0 : U43VA.T 0 = pidn 820 10 := Nat.eq_of_beq_eq_true hh2.2.2.1
  have hrec : ∀ i < U43VA.cnt,
      CFSG.KS.PEnumRC.recMulPtK 820 10 (mask 10) U43VA.GI 5 U43VA.T U43VA.PL i = true :=
    fun i hi => slK_spec (pa (i / 96) (by omega)) i (by change 96 * (i / 96) ≤ i; omega)
      (by change i < 96 * (i / 96) + 96; omega) hi
  have hT : ∀ i < U43VA.cnt, cK (U43VA.T i) = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [hT0]
        exact (PP.id sz).1
      · obtain ⟨hp', hl, e⟩ := CFSG.KS.PEnumRC.recMulPtK_spec (hrec i hi) hi0
        rw [e]
        exact canonK_pcomp (ih _ hp' (by omega)) (gen_tabs.2 _ hl).2
  have hsize : (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL).size = U43VA.cnt - 1 := by
    unfold CFSG.KS.PEnumRC.recParArr
    exact Array.size_ofFn
  have hget : ∀ i < U43VA.cnt - 1, (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL)[i]! =
      (parOf U43VA.PL (i + 1), labOf U43VA.PL (i + 1)) := by
    intro i hi
    unfold CFSG.KS.PEnumRC.recParArr
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have hpar : ∀ i < (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL).size,
      (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL)[i]!.1 ≤ i ∧
      (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL)[i]!.2 < 5 ∧
      U43VA.T (i + 1) = pc (U43VA.T (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL)[i]!.1)
        (U43VA.GI (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL)[i]!.2) := by
    intro i hi
    rw [hsize] at hi
    rw [hget i hi]
    obtain ⟨h1, h2, h3⟩ :=
      CFSG.KS.PEnumRC.recMulPtK_spec (hrec (i + 1) (by omega)) (Nat.succ_ne_zero i)
    exact ⟨Nat.le_of_lt_succ h1, h2, h3⟩
  have hs' : ∀ i < U43VA.cnt, hsortPtK 820 10 (mask 10) U43VA.cnt U43VA.T U43VA.HS U43VA.HSI i =
      true := fun i hi => by
    rw [← hsortPtKF_eq]
    exact slK_spec (ha (i / 288) (by omega)) i (by change 288 * (i / 288) ≤ i; omega)
      (by change i < 288 * (i / 288) + 288; omega) hi
  have hgens : (tabsOf vaCg).all permInvOK = true := by
    rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 5 := by rw [gen_tabs.1] at hj; exact hj
    obtain ⟨hgj, hc⟩ := gen_tabs.2 j hj'
    rw [← getElem!_pos _ j hj, hgj]
    exact U43CoverK.gen_of hc (hinv j hj').2 (hinv j hj').1
  have harr := mulRecArr_unpack gen_tabs (by rw [hT0, idT_tabT, idA_eq sz])
    (fun i hi => hT i (by rw [hsize] at hi; omega)) hpar
  have hdist : hkeysDistinct 820 (Array.ofFn
      (n := (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL).size + 1)
      fun i => tabT (unpack 820 10 (U43VA.T i.val))).toList = true :=
    hkeysDistinct_ofFn (U := fun i => tabT (unpack 820 10 (U43VA.T i))) fun a ha b hb e => by
      rw [hsize] at ha hb
      refine hkeyK_inj hs' a (by omega) b (by omega) ?_
      rw [← hkey_tabT (hT a (by omega)), ← hkey_tabT (hT b (by omega))]
      exact e
  unfold enumRecOK
  rw [hgens, harr, Bool.true_and]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨fun i hi => ⟨(hpar i hi).1, by rw [gen_tabs.1]; exact (hpar i hi).2.1⟩, hdist⟩, ?_⟩
  rw [hsize]
  omega

theorem vaCheck_true : vaCheck (CFSG.KS.PEnumRC.recParArr U43VA.cnt U43VA.PL) = true := by
  obtain ⟨c0, i0, v0⟩ := inF (i := 0) (by decide)
  obtain ⟨c1, i1, v1⟩ := inF (i := 1) (by decide)
  have hz := kZ
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hz
  obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
  unfold vaCheck
  rw [rep8_eq, vaZ_eq, enum_ok]
  simp only [Bool.and_true]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨permOK_unpack c0 v0, U43CoverK.gen_of c1 i1 v1, memCos_of le_rfl (by decide), ?_, ?_, ?_,
    ?_⟩
  · rw [commTT_unpack c1 c0]
    exact hz1
  · rw [idT_tabT, idA_eq sz, tblEq_unpack c1 (PP.id sz).1, hz2]
    rfl
  · rw [tblEq_unpack c1 c0, hz3]
    rfl
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 5 := by rw [gen_tabs.1] at hj; exact hj
    have e : (tabsOf vaCg)[j] = tabT (unpack 820 10 (U43VP (j + 2))) := by
      rw [← getElem!_pos _ j hj, (gen_tabs.2 j hj').1]
      have hh := kHead
      simp only [bAnd_iff] at hh
      have h := allN_spec hh.1 j hj'
      simp only [bAnd_iff] at h
      rw [Nat.eq_of_beq_eq_true h.1]
    have hc := (inF (i := j + 2) (by omega)).1
    have hm := allN_spec kComm j hj'
    simp only [bAnd_iff] at hm
    rw [e, memCos_of (by omega) (by omega), commTT_unpack hc c0, commTT_unpack c1 hc]
    simp only [Bool.true_and, Bool.and_eq_true]
    exact ⟨hm.1, hm.2⟩

end CertificateChecks.KernelHSStd.U43Va

end
