module

public import Certificates.Kernel.Sporadic.OddCore.J2VtxK
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.HSPinned.PairBfsSim
public import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

open CertificateChecks.KernelSpor.J2Vtx in
#kc_forall_chunks vxB1_all (fun k => vxB1 k = true) 64 CertificateChecks.KernelSpor.J2Vtx.vxB1 1

open CertificateChecks.KernelSpor.J2Vtx in
#kc_forall_chunks vxPX_all (fun k => vxPX k = true) 18 CertificateChecks.KernelSpor.J2Vtx.vxPX 1

open CertificateChecks.KernelSpor.J2Vtx in
#kc_forall_chunks vxClX_all (fun k => vxClX k = true) 18 CertificateChecks.KernelSpor.J2Vtx.vxClX 1

namespace CertificateChecks.KernelSpor.J2Vtx

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.J2Cn CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.F112R.St84.J2Model CFSG.Quasithin.F112R.St84.Heis CFSG.Fischer

abbrev Cv (p : Nat) : Prop := canonK 315 9 (mask 9) (315 * 9) p = true

theorem base_parts :
    VxT 0 = wC [2, 1, 2] ∧ VxT 1 = wC [4, 4] ∧ VxT 2 = wC [3, 2, 3, 3] ∧
    VxT 3 = wC [2, 3, 3, 3] ∧ VxT 4 = wC [2, 1, 2] ∧ VxT 5 = wC [1, 4, 3, 4, 3, 2] ∧
    VxT 6 = wC [2, 3] ∧ VxT 7 = wC [1, 2, 4, 2, 1, 4] ∧
    VxT 8 = wP [1, 2, 1, 2, 1, 2, 2, 1, 2, 2] ∧ VxT 9 = wR ∧
    (∀ j < 10, invV (VxT j) (VxI j) = true) ∧ (∀ k < 4, invV (FKc k) (pinv (FKc k)) = true) ∧
    Nat.beq (pc (VxT 0) (VxT 0)) J2Cn.idK = true ∧ Nat.beq (pw 3 (VxT 1)) J2Cn.idK = true ∧
    Nat.beq (pw 5 (pc (VxT 0) (VxT 1))) J2Cn.idK = true ∧
    Nat.beq (pw 3 (VxT 6)) J2Cn.idK = true ∧ Nat.beq (pw 2 (VxT 7)) J2Cn.idK = true ∧
    Nat.beq (pc (VxT 7) (VxT 6)) (pc (VxT 6) (VxT 7)) = true ∧
    conjV 6 βM = true ∧ conjV 9 ρM = true ∧ conjV 7 τM = true ∧ sK (VxT 9) = true ∧
    (∀ i < 64, VxK i = κK (q1mAt i)) ∧
    (∀ i < 64, (decide (q1mAt i = 1) || bIf(Nat.beq (VxK i) J2Cn.idK, false, true)) = true) ∧
    VxA.cnt = 60 ∧ bindV VxA.G VxA.GI [0, 1] = true ∧ penumHdK J2Cn.idK VxA.cnt 200 VxA.T VxA.PL = true ∧
    VxB.cnt = 128 ∧ bindV VxB.G VxB.GI [2, 3, 4, 5, 7] = true ∧
    penumHdK J2Cn.idK VxB.cnt 200 VxB.T VxB.PL = true ∧
    VxC.cnt = 18 ∧ bindV VxC.G VxC.GI [9, 6, 7] = true ∧
    penumHdK J2Cn.idK VxC.cnt 100 VxC.T VxC.PL = true ∧
    VxX.cnt = 1152 ∧ bindV VxX.G VxX.GI [2, 3, 4, 5, 9, 6, 7] = true ∧
    penumHdK J2Cn.idK VxX.cnt 3000 VxX.T VxX.PL = true := by
  have h := vx_base
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9,
    Nat.eq_of_beq_eq_true h10, fun j hj => allN_spec h11 j hj, fun k hk => allN_spec h12 k hk,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    fun i hi => Nat.eq_of_beq_eq_true (allN_spec h23 i hi), fun i hi => allN_spec h24 i hi,
    Nat.eq_of_beq_eq_true h25, h26, h27, Nat.eq_of_beq_eq_true h28, h29, h30,
    Nat.eq_of_beq_eq_true h31, h32, h33, Nat.eq_of_beq_eq_true h34, h35, h36⟩

theorem invV_spec {p r : Nat} (h : invV p r = true) :
    Cv p ∧ Cv r ∧ invEqK 315 9 (mask 9) (315 * 9) p r = true := by
  unfold invV at h
  simp only [bAnd_iff] at h
  exact h

theorem vc {j : Nat} (hj : j < 10) : Cv (VxT j) := (invV_spec (base_parts.2.2.2.2.2.2.2.2.2.2.1 j hj)).1

theorem vinv {j : Nat} (hj : j < 10) : invEqK 315 9 (mask 9) (315 * 9) (VxT j) (VxI j) = true ∧
    Cv (VxI j) :=
  ⟨(invV_spec (base_parts.2.2.2.2.2.2.2.2.2.2.1 j hj)).2.2,
    (invV_spec (base_parts.2.2.2.2.2.2.2.2.2.2.1 j hj)).2.1⟩

abbrev TU (x : Table) (p : Nat) : Prop := x = tabT (unpack 315 9 p) ∧ Cv p

theorem wC_eq {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 4) : TU (wordTbl 315 j2C2Gens wd) (wC wd) :=
  wordTbl_unpack hid hidc fun l hl => by
    obtain ⟨h1, h2⟩ := hw l hl
    have e : j2C2Gens.getD (l - 1) (idT 315) = j2CentTbl (31 + l) := by
      rcases (by omega : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4) with rfl | rfl | rfl | rfl <;> rfl
    rw [e]
    exact ⟨tabF (k := 31 + l) (by omega), Fc (k := 31 + l) (by omega)⟩

theorem wP_eq {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 2) :
    TU (wordTbl 315 j2PGTbls.toList wd) (wP wd) :=
  wordTbl_unpack hid hidc fun l hl => by
    obtain ⟨h1, h2⟩ := hw l hl
    have hsz : j2PGTbls.size = 2 := rfl
    have hs : l - 1 < j2PGTbls.size := by rw [hsz]; omega
    have e : j2PGTbls.toList.getD (l - 1) (idT 315) = j2PGTbls[l - 1]! := by
      rw [List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact hs), Array.getElem_toList,
        getElem!_pos j2PGTbls (l - 1) hs]
    rw [e]
    exact ⟨(pg_tabs.2 (l - 1) (by omega)).1, Sc (j := l - 1) (by omega)⟩

theorem c2aT_eq : TU (c2aT ()) (VxT 0) := by rw [base_parts.1]; exact wC_eq (by decide)
theorem c2bT_eq : TU (c2bT ()) (VxT 1) := by rw [base_parts.2.1]; exact wC_eq (by decide)
theorem e1T_eq : TU (e1T ()) (VxT 2) := by rw [base_parts.2.2.1]; exact wC_eq (by decide)
theorem e2T_eq : TU (e2T ()) (VxT 3) := by rw [base_parts.2.2.2.1]; exact wC_eq (by decide)
theorem f1T_eq : TU (f1T ()) (VxT 4) := by rw [base_parts.2.2.2.2.1]; exact wC_eq (by decide)
theorem f2T_eq : TU (f2T ()) (VxT 5) := by rw [base_parts.2.2.2.2.2.1]; exact wC_eq (by decide)
theorem bmT_eq : TU (bmT ()) (VxT 6) := by rw [base_parts.2.2.2.2.2.2.1]; exact wC_eq (by decide)
theorem tmT_eq : TU (tmT ()) (VxT 7) := by rw [base_parts.2.2.2.2.2.2.2.1]; exact wC_eq (by decide)
theorem yT_eq : TU (yT ()) (VxT 8) := by rw [base_parts.2.2.2.2.2.2.2.2.1]; exact wP_eq (by decide)

theorem rmT_eq : TU (rmT ()) (VxT 9) := by
  rw [base_parts.2.2.2.2.2.2.2.2.2.1]
  refine wordTbl_unpack hid hidc fun l hl => ?_
  have hl' : l = 1 ∨ l = 4 ∨ l = 7 ∨ l = 5 ∨ l = 6 := by simpa using hl
  rcases hl' with rfl | rfl | rfl | rfl | rfl
  · have e : lR 1 = VxT 2 := by unfold lR; rfl
    rw [e]
    simp only [Nat.sub_self, List.getD_cons_zero]
    exact e1T_eq
  · have e : lR 4 = VxT 5 := by unfold lR; rfl
    rw [e]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
    exact f2T_eq
  · have e : lR 7 = VxT 8 := by unfold lR; rfl
    rw [e]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
    exact yT_eq
  · have e : lR 5 = VxT 7 := by unfold lR; rfl
    rw [e]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
    exact tmT_eq
  · have e : lR 6 = VxT 6 := by unfold lR; rfl
    rw [e]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
    exact bmT_eq

theorem inv_eq {x : Table} {p r : Nat} (hx : TU x p) (h : invEqK 315 9 (mask 9) (315 * 9) p r = true)
    (hr : Cv r) : TU (invT 315 x) r :=
  ⟨by rw [hx.1]; exact invT_unpack (by norm_num) h, hr⟩

theorem comp_eq {x y : Table} {p q : Nat} (hx : TU x p) (hy : TU y q) : TU (compT 315 x y) (pc p q) :=
  ⟨by rw [hx.1, hy.1]; exact compT_unpack hx.2 hy.2, canonK_pcomp hx.2 hy.2⟩

theorem pow_eq {x : Table} {p : Nat} (hx : TU x p) (e : Nat) : TU (powT 315 e x) (pw e p) :=
  ⟨by rw [hx.1]; exact powT_unpack (pows p) hid hidc hx.2 e, canonP hx.2 e⟩

theorem tblEq_eq {x y : Table} {p q : Nat} (hx : TU x p) (hy : TU y q) :
    tblEq 315 x y = Nat.beq p q := by
  rw [hx.1, hy.1]
  exact tblEq_unpack hx.2 hy.2

theorem idT_eq : TU (idT 315) J2Cn.idK := ⟨hid, hidc⟩

theorem perm_eq {x : Table} {j : Nat} (hj : j < 10) (hx : TU x (VxT j)) : permOK 315 x = true := by
  rw [hx.1]
  exact permOK_unpack hx.2 (vinv hj).1

theorem pw_mod (k : Nat) {x : Table} {p : Nat} (hx : TU x p) : TU (powT 315 k x) (pw k p) := pow_eq hx k

theorem EmT_eq (a : F4) : TU (EmT a) (EKc a.code.val) :=
  comp_eq (pow_eq e1T_eq _) (pow_eq e2T_eq _)

theorem FmT_eq (b : F4) : TU (FmT b) (FKc b.code.val) :=
  comp_eq (pow_eq f1T_eq _) (pow_eq f2T_eq _)

theorem commFT_eq (b : F4) : TU (commFT b) (CFc b.code.val) := by
  have hk : b.code.val < 4 := b.code.isLt
  have hi := invV_spec (base_parts.2.2.2.2.2.2.2.2.2.2.2.1 _ hk)
  exact comp_eq (comp_eq (comp_eq e1T_eq (FmT_eq b)) (inv_eq e1T_eq (vinv (by norm_num)).1
    (vinv (by norm_num)).2)) (inv_eq (FmT_eq b) hi.2.2 hi.2.1)

theorem κT_eq (q : Q1M) : TU (κT q) (κK q) :=
  comp_eq (comp_eq (EmT_eq q.a) (FmT_eq q.b)) (commFT_eq _)

theorem κK_idx (q : Q1M) : κK q = VxK (q1mIdx q) := by
  rw [base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (q1mIdx_lt q), q1mAt_q1mIdx]

theorem κT_idx (q : Q1M) : TU (κT q) (VxK (q1mIdx q)) := by
  rw [← κK_idx]
  exact κT_eq q

theorem ks_eq {i : Nat} (hi : i < 64) : TU ((κArr ())[i]!) (VxK i) := by
  rw [κArr_getElem i hi]
  have := κT_idx (q1mAt i)
  have e : q1mIdx (q1mAt i) = i := by
    unfold q1mIdx q1mAt
    simp only
    omega
  rwa [e] at this

theorem bIf_ft (c : Bool) : bIf(c, false, true) = !c := by cases c <;> rfl

theorem a1_true : a1OK = true := by
  simp only [a1OK, a1Checks, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [perm_eq (by norm_num) c2aT_eq, perm_eq (by norm_num) c2bT_eq]
  rfl

theorem a2_true : a2OK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, s1, s2, s3, -⟩ := base_parts
  simp only [a2OK, a2Checks, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [tblEq_eq (comp_eq c2aT_eq c2aT_eq) idT_eq, tblEq_eq (pow_eq c2bT_eq 3) idT_eq,
    tblEq_eq (pow_eq (comp_eq c2aT_eq c2bT_eq) 5) idT_eq, s1, s2, s3]
  rfl

theorem b0_true : b0OK = true := by
  simp only [b0OK, b0Tbls, List.all_cons, List.all_nil, Bool.and_true]
  rw [perm_eq (by norm_num) e1T_eq, perm_eq (by norm_num) e2T_eq, perm_eq (by norm_num) f1T_eq,
    perm_eq (by norm_num) f2T_eq, perm_eq (by norm_num) bmT_eq, perm_eq (by norm_num) tmT_eq,
    perm_eq (by norm_num) yT_eq, perm_eq (by norm_num) rmT_eq]
  rfl

theorem b1_true : b1OK = true := by
  have hn1 := base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold b1OK
  simp only [Bool.and_eq_true]
  refine ⟨CFSG.KC.HSPinnedBfs.allIn_iff'.2 fun i _ hi => CFSG.KC.HSPinnedBfs.allIn_iff'.2
    fun j _ hj => ?_, CFSG.KC.HSPinnedBfs.allIn_iff'.2 fun i _ hi => ?_⟩
  · have hq := q1mIdx_lt (q1mAt i * q1mAt j)
    rw [tblEq_eq (ks_eq hq) (comp_eq (ks_eq hi) (ks_eq hj))]
    exact allN_spec (vxB1_all i hi) j hj
  · have h := hn1 i hi
    rw [bIf_ft] at h
    rw [tblEq_eq (ks_eq hi) idT_eq]
    exact h

theorem conjV_of {c : Table} {j : Nat} (hj : j < 10) (hc : TU c (VxT j)) {α : MulAut Q1M}
    (h : conjV j α = true) : conjGenOK c α = true := by
  unfold conjGenOK
  unfold conjV at h
  rw [List.all_eq_true] at h ⊢
  intro g hg
  have hci := inv_eq hc (vinv hj).1 (vinv hj).2
  unfold conjT
  rw [tblEq_eq (comp_eq (comp_eq hc (κT_idx g)) hci) (κT_idx (α g))]
  exact h g hg

theorem b2_true : b2OK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c1, c2, c3, -⟩ := base_parts
  simp only [b2OK, b2Checks, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [conjV_of (by norm_num) bmT_eq c1, conjV_of (by norm_num) rmT_eq c2,
    conjV_of (by norm_num) tmT_eq c3]
  rfl

theorem b3_true : b3OK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s1, s2, s3, -⟩ := base_parts
  simp only [b3OK, b3Checks, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [tblEq_eq (pow_eq bmT_eq 3) idT_eq, tblEq_eq (pow_eq tmT_eq 2) idT_eq,
    tblEq_eq (comp_eq tmT_eq bmT_eq) (comp_eq bmT_eq tmT_eq), s1, s2, s3]
  rfl

theorem b5_true : b5OK = true := by
  unfold b5OK
  rw [rmT_eq.1, sift_eq rmT_eq.2]
  exact base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bind_spec {G GI : Nat → Nat} {ix : List Nat} (h : bindV G GI ix = true) :
    ∀ j < ix.length, G j = J2Cn.idK ∧ GI j = VxT (ix.getD j 0) := by
  intro j hj
  have := allN_spec h j hj
  simp only [bAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem tabs_of {L : List Table} {ix : List Nat} {GI : Nat → Nat} (hl : L.length = ix.length)
    (hix : ∀ j < ix.length, ix.getD j 0 < 10)
    (hb : ∀ j < ix.length, GI j = VxT (ix.getD j 0))
    (hL : ∀ j (hj : j < L.length), TU L[j] (VxT (ix.getD j 0))) :
    TabsOK 315 9 ix.length GI L.toArray := by
  refine ⟨by simp [hl], fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simp [hl, hj]), List.getElem_toArray, hb j hj]
  exact hL j (by omega)

theorem invs_of {ix : List Nat} {GI : Nat → Nat} (hix : ∀ j < ix.length, ix.getD j 0 < 10)
    (hb : ∀ j < ix.length, GI j = VxT (ix.getD j 0)) :
    ∀ j < ix.length, invEqK 315 9 (mask 9) (315 * 9) (GI j) (invOf ix j) = true ∧
      Cv (invOf ix j) := fun j hj => by
  rw [hb j hj]
  exact vinv (hix j hj)

theorem enumOf {L : List Table} {ix : List Nat} {cap m cnt : Nat}
    {G GI T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hl : L.length = ix.length) (hix : ∀ j < ix.length, ix.getD j 0 < 10)
    (hL : ∀ j (hj : j < L.length), TU L[j] (VxT (ix.getD j 0)))
    (hcnt : cnt = m) (hb : bindV G GI ix = true) (hh : penumHdK J2Cn.idK cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK 315 9 (mask 9) (315 * 9) true G GI ix.length cnt T PL POS SRT SRI i =
      true)
    (hs : ∀ i < cnt, hsortPtK 315 9 (mask 9) cnt T HS HSI i = true)
    (hc : ∀ c < cnt * (ix.length + ix.length), findPtK cnt T
      (prodQK 315 9 (mask 9) (ix.length + ix.length) T (bothK ix.length GI (invOf ix))) CL c =
        true) :
    enumOK 315 cap m L = true := by
  have hb' := bind_spec hb
  exact enumOK_of hn (fun j hj => (hb' j hj).1)
    (tabs_of hl hix (fun j hj => (hb' j hj).2) hL)
    (invs_of hix fun j hj => (hb' j hj).2) hh hp hs hc hcnt

theorem a3_true : a3OK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ca, ba, ha, -⟩ :=
    base_parts
  have h := vxA0
  unfold vxA at h
  simp only [bAnd_iff] at h
  obtain ⟨p, s, c⟩ := h
  unfold a3OK
  refine enumOf (L := [c2aT (), c2bT ()]) (ix := [0, 1]) rfl (by decide) (fun j hj => ?_) ca ba ha
    (fun i hi => penumSl_spec p i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec s i (Nat.zero_le _) (by omega) hi)
    (fun c' hc => by
      have h4 : c' < VxA.cnt * 4 := hc
      exact slK_spec c c' (Nat.zero_le _) (by omega) (by change c' < VxA.cnt * 4; omega))
  have hj' : j < 2 := hj
  interval_cases j
  · exact c2aT_eq
  · exact c2bT_eq

theorem b4_true : b4OK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, cb, bb, hb,
    cc, bc, hc, cx, bx, hx⟩ := base_parts
  have eB : enumOK 315 200 128 [e1T (), e2T (), f1T (), f2T (), tmT ()] = true := by
    have hP : ∀ k < 2, vxPB k = true := by
      intro k hk
      interval_cases k
      exacts [vxPB0, vxPB1]
    have hC : ∀ k < 2, vxClB k = true := by
      intro k hk
      interval_cases k
      exacts [vxClB0, vxClB1]
    refine enumOf (L := [e1T (), e2T (), f1T (), f2T (), tmT ()]) (ix := [2, 3, 4, 5, 7])
      (POS := VxB.POS) (SRT := VxB.SRT) (SRI := VxB.SRI) (HS := VxB.HS) (HSI := VxB.HSI)
      (CL := VxBCl) rfl (by decide) (fun j hj => ?_) cb bb hb
      (fun i hi => ?_) (fun i hi => ?_) (fun c' hc' => ?_)
    · have hj' : j < 5 := hj
      interval_cases j
      exacts [e1T_eq, e2T_eq, f1T_eq, f2T_eq, tmT_eq]
    · have h := hP (i / 64) (by omega)
      unfold vxPB at h
      simp only [bAnd_iff] at h
      exact penumSl_spec h.1 i (by change 64 * (i / 64) ≤ i; omega)
        (by change i < 64 * (i / 64) + 64; omega) hi
    · have h := hP (i / 64) (by omega)
      unfold vxPB at h
      simp only [bAnd_iff] at h
      exact slK_spec h.2 i (by change 64 * (i / 64) ≤ i; omega)
        (by change i < 64 * (i / 64) + 64; omega) hi
    · have h10 : c' < VxB.cnt * 10 := hc'
      exact slK_spec (hC (c' / 640) (by omega)) c' (by change 640 * (c' / 640) ≤ c'; omega)
        (by change c' < 640 * (c' / 640) + 640; omega) (by change c' < VxB.cnt * 10; omega)
  have eC : enumOK 315 100 18 [rmT (), bmT (), tmT ()] = true := by
    have h := vxC0
    unfold vxC at h
    simp only [bAnd_iff] at h
    obtain ⟨p, s, c⟩ := h
    refine enumOf (L := [rmT (), bmT (), tmT ()]) (ix := [9, 6, 7]) rfl (by decide) (fun j hj => ?_)
      cc bc hc
      (fun i hi => penumSl_spec p i (Nat.zero_le _) (by omega) hi)
      (fun i hi => slK_spec s i (Nat.zero_le _) (by omega) hi)
      (fun c' hc' => by
        have h6 : c' < VxC.cnt * 6 := hc'
        exact slK_spec c c' (Nat.zero_le _) (by omega) (by change c' < VxC.cnt * 6; omega))
    have hj' : j < 3 := hj
    interval_cases j
    exacts [rmT_eq, bmT_eq, tmT_eq]
  have eX : enumOK 315 3000 1152 [e1T (), e2T (), f1T (), f2T (), rmT (), bmT (), tmT ()] = true := by
    refine enumOf (L := [e1T (), e2T (), f1T (), f2T (), rmT (), bmT (), tmT ()])
      (ix := [2, 3, 4, 5, 9, 6, 7])
      (POS := VxX.POS) (SRT := VxX.SRT) (SRI := VxX.SRI) (HS := VxX.HS) (HSI := VxX.HSI)
      (CL := VxXCl) rfl (by decide) (fun j hj => ?_) cx bx hx
      (fun i hi => ?_) (fun i hi => ?_) (fun c' hc' => ?_)
    · have hj' : j < 7 := hj
      interval_cases j
      exacts [e1T_eq, e2T_eq, f1T_eq, f2T_eq, rmT_eq, bmT_eq, tmT_eq]
    · have h18 : i / 64 < 18 := by omega
      have h := vxPX_all (i / 64) h18
      unfold vxPX at h
      simp only [bAnd_iff] at h
      exact penumSl_spec h.1 i (by change 64 * (i / 64) ≤ i; omega)
        (by change i < 64 * (i / 64) + 64; omega) hi
    · have h18 : i / 64 < 18 := by omega
      have h := vxPX_all (i / 64) h18
      unfold vxPX at h
      simp only [bAnd_iff] at h
      exact slK_spec h.2 i (by change 64 * (i / 64) ≤ i; omega)
        (by change i < 64 * (i / 64) + 64; omega) hi
    · have h14 : c' < VxX.cnt * 14 := hc'
      have h18 : c' / 896 < 18 := by omega
      exact slK_spec (vxClX_all (c' / 896) h18) c' (by change 896 * (c' / 896) ≤ c'; omega)
        (by change c' < 896 * (c' / 896) + 896; omega) (by change c' < VxX.cnt * 14; omega)
  simp only [b4OK, b4Checks, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [eB, eC, eX]
  rfl

theorem vx_neg_word : (!Nat.beq (VxT 0) (wC [4, 4])) = true := by quickRfl

theorem vx_neg_kappa : (!Nat.beq (VxK (q1mIdx (q1mAt 1 * q1mAt 4))) (pc (VxK 4) (VxK 1)) ||
    Nat.beq (pc (VxK 1) (VxK 4)) (pc (VxK 4) (VxK 1))) = true := by quickRfl

theorem vx_neg_pos : (!findPtK VxA.cnt VxA.T
    (prodQK 315 9 (mask 9) 4 VxA.T (bothK 2 VxA.GI (invOf [0, 1]))) (fun c => VxACl (c + 1)) 0) =
    true := by quickRfl

theorem j2vtx_all : (a1OK = true) ∧ (a2OK = true) ∧ (a3OK = true) ∧ (b0OK = true) ∧
    (b1OK = true) ∧ (b2OK = true) ∧ (b3OK = true) ∧ (b4OK = true) ∧ (b5OK = true) :=
  ⟨a1_true, a2_true, a3_true, b0_true, b1_true, b2_true, b3_true, b4_true, b5_true⟩

end CertificateChecks.KernelSpor.J2Vtx

end
