module

public import Certificates.Kernel.Sporadic.OddCore.SuzRKC0
public import Certificates.Kernel.Sporadic.OddCore.SuzRKC1
public import Certificates.Kernel.Sporadic.OddCore.SuzRKC2
public import Certificates.Kernel.Sporadic.OddCore.SuzRKC3
public import CFSG.Certificates.Kernel.Spor.KEnumSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound

public section

namespace CertificateChecks.KernelSpor.SuzRKF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.KEnum CFSG.KS.KeyBfsG CFSG.KS.FpBfs
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.RootTwistCheck
open CFSG.Sporadic.SuzRecog.RootTwistData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzRKC

theorem kGenA_eq : kGenAArr = unpack 1782 11 (SuzRKG 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzRKA.all 0 (by norm_num)
  rw [← SuzRKA.eq, Nat.mul_zero, Nat.eq_of_beq_eq_true gA] at h
  exact h

theorem kGenB_eq : kGenBArr = unpack 1782 11 (SuzRKG 1) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzRKB.all 0 (by norm_num)
  rw [← SuzRKB.eq, Nat.mul_zero, Nat.eq_of_beq_eq_true gB] at h
  exact h

theorem kGens_eq {s : Nat} (hs : s < 4) : kGens[s]! = unpack 1782 11 (SuzRKG s) := by
  interval_cases s
  · simp only [kGens, List.getElem!_toArray, List.getElem!_cons_zero]
    exact kGenA_eq
  · simp only [kGens, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact kGenB_eq
  · simp only [kGens, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [kGenA_eq]
    exact (invEqK_sound iA).1
  · simp only [kGens, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [kGenB_eq]
    exact (invEqK_sound iB).1

theorem idA_eq : idA 1782 = unpack 1782 11 (pidn 1782 11) := (idK_sound idn).symm

theorem kSearch_eq : kSearch = keyBfsG CFSG.Sporadic.SuzRecog.LevelTwo.fp
    (fun s x => compA 1782 kGens[s]! x) 2 (idA 1782)
    (CFSG.Sporadic.SuzRecog.LevelTwo.fp (idA 1782)) 3456 := rfl

theorem pt_of {lo len i : Nat}
    (h : kenumSlK 1782 11 (mask 11) (1782 * 11) 2 4 3456 SuzRKG SuzRKT SuzRKTI SuzRKPL SuzRKPOS
      SuzRKFP SuzRKSRT SuzRKSRI lo len = true) (h1 : lo ≤ i) (h2 : i < lo + len) (h3 : i < 3456) :
    kenumPtK 1782 11 (mask 11) (1782 * 11) 2 4 3456 SuzRKG SuzRKT SuzRKTI SuzRKPL SuzRKPOS SuzRKFP
      SuzRKSRT SuzRKSRI i = true := by
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i 3456 = true := by simpa [Nat.blt_eq] using h3
  rw [hb] at h'
  exact h'

theorem pts : ∀ i < 3456, kenumPtK 1782 11 (mask 11) (1782 * 11) 2 4 3456 SuzRKG SuzRKT SuzRKTI
    SuzRKPL SuzRKPOS SuzRKFP SuzRKSRT SuzRKSRI i = true := by
  intro i hi
  have hs : ∀ s < 48, sl s = true := by
    intro s hs
    interval_cases s
    exacts [sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11, sl12, sl13, sl14, sl15,
      sl16, sl17, sl18, sl19, sl20, sl21, sl22, sl23, sl24, sl25, sl26, sl27, sl28, sl29, sl30,
      sl31, sl32, sl33, sl34, sl35, sl36, sl37, sl38, sl39, sl40, sl41, sl42, sl43, sl44, sl45,
      sl46, sl47]
  have h := hs (i / 72) (by omega)
  unfold sl at h
  exact pt_of h (by change 72 * (i / 72) ≤ i; omega) (by change i < 72 * (i / 72) + 72; omega) hi

theorem rec :
    keyBfsG CFSG.Sporadic.SuzRecog.LevelTwo.fp (fun s x => compA 1782 kGens[s]! x) 2 (idA 1782)
        (CFSG.Sporadic.SuzRecog.LevelTwo.fp (idA 1782)) 3456 =
        (Array.ofFn (n := 3456) fun i => unpack 1782 11 (SuzRKT i.val),
          Array.ofFn (n := 3456) fun i => if i.val = 0 then 0 else SuzRKPL i.val / 2,
          Array.ofFn (n := 3456) fun i => if i.val = 0 then 0 else SuzRKPL i.val % 2) ∧
      (∀ i < 3456, ∀ s < 4, SuzRKPOS (4 * i + s) < 3456 ∧
        compA 1782 kGens[s]! (unpack 1782 11 (SuzRKT i)) =
          unpack 1782 11 (SuzRKT (SuzRKPOS (4 * i + s)))) ∧
      (∀ i < 3456, invCand 1782 (unpack 1782 11 (SuzRKT i)) = unpack 1782 11 (SuzRKTI i) ∧
        isInvA 1782 (unpack 1782 11 (SuzRKT i)) (unpack 1782 11 (SuzRKTI i)) = true) ∧
      (∀ a < 3456, ∀ b < 3456, CFSG.Sporadic.SuzRecog.LevelTwo.fp (unpack 1782 11 (SuzRKT a)) =
        CFSG.Sporadic.SuzRecog.LevelTwo.fp (unpack 1782 11 (SuzRKT b)) → a = b) ∧
      (∀ i < 3456, 0 < i → SuzRKPL i / 2 < i ∧ SuzRKPL i % 2 < 2 ∧
        compA 1782 kGens[SuzRKPL i % 2]! (unpack 1782 11 (SuzRKT (SuzRKPL i / 2))) =
          unpack 1782 11 (SuzRKT i)) ∧
      (∀ i < 3456, canonK 1782 11 (mask 11) (1782 * 11) (SuzRKT i) = true) ∧
      (∀ s < 4, canonK 1782 11 (mask 11) (1782 * 11) (SuzRKG s) = true) :=
  kenumK_sound (k := 2) (kk := 4) (cnt := 3456) (cap := 3456)
    (gens := kGens) (root := idA 1782) (fun _ hs => kGens_eq hs) idA_eq hd pts le_rfl

theorem kEls_eq : kEls = Array.ofFn (n := 3456) fun i => unpack 1782 11 (SuzRKT i.val) := by
  unfold kEls
  rw [kSearch_eq, rec.1]

theorem kEls_get {i : Nat} (hi : i < 3456) : kEls[i]! = unpack 1782 11 (SuzRKT i) := by
  rw [kEls_eq, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem kPar_get {i : Nat} (hi : i < 3456) (h0 : 0 < i) : kPar[i]! = SuzRKPL i / 2 := by
  unfold kPar
  rw [kSearch_eq, rec.1, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  simp [Nat.pos_iff_ne_zero.1 h0]

theorem kLab_get {i : Nat} (hi : i < 3456) (h0 : 0 < i) : kLab[i]! = SuzRKPL i % 2 := by
  unfold kLab
  rw [kSearch_eq, rec.1, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  simp [Nat.pos_iff_ne_zero.1 h0]

theorem kEls_size : kEls.size = 3456 := by
  rw [kEls_eq, Array.size_ofFn]

theorem kEls_inj : ∀ a < kEls.size, ∀ b < kEls.size,
    CFSG.Sporadic.SuzRecog.LevelTwo.fp kEls[a]! = CFSG.Sporadic.SuzRecog.LevelTwo.fp kEls[b]! →
      a = b := by
  intro a ha b hb e
  rw [kEls_size] at ha hb
  rw [kEls_get ha, kEls_get hb] at e
  exact rec.2.2.2.1 a ha b hb e

theorem kTab_eq : kTab = keyTab CFSG.Sporadic.SuzRecog.LevelTwo.fp kEls := rfl

theorem kTab_get {j : Nat} (hj : j < 3456) :
    kTab.getD (CFSG.Sporadic.SuzRecog.LevelTwo.fp kEls[j]!) 3456 = j := by
  rw [kTab_eq]
  exact keyTab_getD kEls_inj (by rw [kEls_size]; exact hj) 3456

theorem eqA_self (t : Array Nat) : eqA 1782 t t = true := by
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem kStep_true {i s : Nat} (hi : i < 3456) (hs : s < 4) : kStep i s = true := by
  obtain ⟨hq, he⟩ := rec.2.1 i hi s hs
  have hy : compA 1782 kGens[s]! kEls[i]! = kEls[SuzRKPOS (4 * i + s)]! := by
    rw [kEls_get hi, he, kEls_get hq]
  unfold kStep
  simp only []
  rw [hy, kTab_get hq, eqA_self, Bool.and_true]
  exact decide_eq_true hq

theorem kEnumOK_true : kEnumOK = true := by
  unfold kEnumOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨kEls_size, ?_⟩, ?_⟩
  · have h := hd
    unfold kenumHdK at h
    simp only [bAnd_iff] at h
    rw [kEls_get (by norm_num), Nat.eq_of_beq_eq_true h.2.2.2.1, ← idA_eq]
    exact eqA_self _
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  obtain ⟨hinv1, hinv2⟩ := rec.2.2.1 i hi
  refine ⟨⟨⟨?_, kTab_get hi⟩, ?_⟩, ?_⟩
  · unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permOK
    rw [kEls_get hi, hinv1]
    exact hinv2
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · right
      obtain ⟨t1, t2, t3⟩ := rec.2.2.2.2.1 i hi h0
      rw [kPar_get hi h0, kLab_get hi h0]
      refine ⟨⟨t1, t2⟩, ?_⟩
      rw [kEls_get hi, kEls_get (by omega), t3]
      exact eqA_self _
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro s hs
    exact kStep_true hi hs

end CertificateChecks.KernelSpor.SuzRKF

end
