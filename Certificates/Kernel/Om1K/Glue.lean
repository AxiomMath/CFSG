module

public import Certificates.Kernel.Om1K.ChecksV
public import Certificates.Kernel.Om1K.ChecksR
public import Certificates.Kernel.Om1K.ChecksE
public import Certificates.Kernel.Om2K.Rel
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import Certificates.Data.Holder1711.Om1Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CertificateChecks.KernelOm2 (pc2 wAK)
open CertificateChecks.KernelLC.E8 (RT FT NEG)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (Om1Facts.E Om1Facts.G Om1Facts.e
  Om1Facts.t Om1Facts.ta Om1Facts.tb Om1Facts.tc Om1Facts.z Om1Facts.R)

abbrev PR (P : Nat) (g : Equiv.Perm (Fin 240)) : Prop := PRep 240 8 P g

theorem pr_ip {P : Nat} {g : Equiv.Perm (Fin 240)} (h : PR P g) (x : Fin 240) :
    pg 8 (mask 8) P x = g x := h x

theorem pr_pc {P Q : Nat} {g h : Equiv.Perm (Fin 240)} (hP : PR P g) (hQ : PR Q h) :
    PR (pc2 P Q) (g * h) := prep_pcomp (by norm_num) hP hQ

theorem pr_pid : PR (pidn 240 8) 1 := prep_pidn (by norm_num) (by norm_num)

theorem pr_eq {P : Nat} {g h : Equiv.Perm (Fin 240)} (hg : PR P g) (hh : PR P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem pr_of_permOK {P Q : Nat} (h : permOK 240 8 (mask 8) (240 * 8) P Q = true) :
    PR P (permOfArr 240 (unpack 240 8 P)) :=
  prep_of_rep (rep_permOfArr (isInvA_unpack h)).1

theorem pr_RT {r : Nat} (hr : r < 240) : PR (RT r) (permOfArr 240 (unpack 240 8 (RT r))) :=
  pr_of_permOK (allN_spec A.kRTv r hr)

theorem pr_wAK : ∀ w : List Nat, (∀ r ∈ w, r < 240) →
    PR (wAK w) (w.map fun r => permOfArr 240 (unpack 240 8 (RT r))).prod
  | [], _ => by
    change PR (pidn 240 8) _
    rw [List.map_nil, List.prod_nil]
    exact pr_pid
  | r :: w, h => by
    change PR (pc2 (RT r) (wAK w)) _
    rw [List.map_cons, List.prod_cons]
    exact pr_pc (pr_RT (h r (List.mem_cons_self ..)))
      (pr_wAK w fun s hs => h s (List.mem_cons_of_mem _ hs))

theorem E_prod {w : List Nat} (hw : ∀ r ∈ w, r < 240) :
    Om1Facts.E w = (w.map fun r => permOfArr 240 (unpack 240 8 (RT r))).prod := by
  unfold Om1Facts.E
  rw [(KernelOm2.wA_eq w hw).1]
  exact permOfArr_eq_of_rep (rep_unpack (pr_wAK w hw))

theorem pr_E {w : List Nat} (hw : ∀ r ∈ w, r < 240) : PR (wAK w) (Om1Facts.E w) := by
  rw [E_prod hw]
  exact pr_wAK w hw

theorem E_append {a b : List Nat} (ha : ∀ r ∈ a, r < 240) (hb : ∀ r ∈ b, r < 240) :
    Om1Facts.E (a ++ b) = Om1Facts.E a * Om1Facts.E b := by
  have hab : ∀ r ∈ a ++ b, r < 240 := fun r hr => (List.mem_append.1 hr).elim (ha r) (hb r)
  rw [E_prod hab, E_prod ha, E_prod hb, List.map_append, List.prod_append]

theorem pr_e {m : Nat} (hm : m < 256) : PR (FT m) (Om1Facts.e m) := by
  unfold Om1Facts.e
  rw [KernelOm2.eA_eq hm]
  exact pr_of_permOK (allN_spec A.kFTv m hm)

theorem pr_z : PR NEG Om1Facts.z := by
  unfold Om1Facts.z zA
  rw [CertificateChecks.KernelLC.E8.neg_eq]
  exact pr_of_permOK A.kNEGv

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem getD_mem {ws : List (List Nat)} {k : Nat} (hk : k < ws.length) : ws.getD k [] ∈ ws := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem mem_getD {ws : List (List Nat)} {w : List Nat} (hw : w ∈ ws) :
    ∃ k < ws.length, ws.getD k [] = w := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hw
  exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk, e]⟩

theorem E_mem_G {ws : List (List Nat)} {w : List Nat} (hw : w ∈ ws) :
    Om1Facts.E w ∈ Om1Facts.G ws :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem words_lt : ∀ w ∈ allWords ++ A.wXr ++ A.k0W ++ A.elW, ∀ r ∈ w, r < 240 := by decide +kernel

theorem lt_of_sub {ws : List (List Nat)} (hs : ∀ w ∈ ws, w ∈ allWords ++ A.wXr ++ A.k0W ++ A.elW) :
    ∀ w ∈ ws, ∀ r ∈ w, r < 240 := fun w hw => words_lt w (hs w hw)

theorem tab_pr {ws : List (List Nat)} {G : Nat → Nat} {n : Nat}
    (hc : allN n (fun k => Nat.beq (G k) (wAK (ws.getD k []))) = true)
    (hlt : ∀ w ∈ ws, ∀ r ∈ w, r < 240) (hn : ws.length = n) {k : Nat} (hk : k < n) :
    PR (G k) (Om1Facts.E (ws.getD k [])) := by
  rw [Nat.eq_of_beq_eq_true (allN_spec hc k hk)]
  exact pr_E (hlt _ (getD_mem (by omega)))

theorem elW_lt : ∀ w ∈ A.elW, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wT_lt : ∀ w ∈ wT, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wCa_lt : ∀ w ∈ wCa, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wCc_lt : ∀ w ∈ wCc, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wSub_lt : ∀ w ∈ wSub, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wX_lt : ∀ w ∈ wX, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wXr_lt : ∀ w ∈ A.wXr, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)

theorem pr_EL {k : Nat} (hk : k < 6) : PR (A.EL.G k) (Om1Facts.E (A.elW.getD k [])) :=
  tab_pr A.kEL elW_lt A.kLens.1 hk

theorem pr_TG {k : Nat} (hk : k < 7) : PR (A.TG.G k) (Om1Facts.E (wT.getD k [])) :=
  tab_pr A.kTG wT_lt A.kLens.2.1 hk

theorem pr_CA {k : Nat} (hk : k < 8) : PR (A.CA.G k) (Om1Facts.E (wCa.getD k [])) :=
  tab_pr A.kCA wCa_lt A.kLens.2.2.1 hk

theorem pr_CC {k : Nat} (hk : k < 5) : PR (A.CC.G k) (Om1Facts.E (wCc.getD k [])) :=
  tab_pr A.kCC wCc_lt A.kLens.2.2.2.1 hk

theorem pr_WS {k : Nat} (hk : k < 8) : PR (A.WS.G k) (Om1Facts.E (wSub.getD k [])) :=
  tab_pr A.kWS wSub_lt A.kLens.2.2.2.2.1 hk

theorem pr_XG {k : Nat} (hk : k < 7) : PR (A.XG.G k) (Om1Facts.E (wX.getD k [])) :=
  tab_pr A.kXG wX_lt A.kLens.2.2.2.2.2.1 hk

theorem pr_XI {k : Nat} (hk : k < 7) : PR (A.XI.G k) (Om1Facts.E (A.wXr.getD k [])) :=
  tab_pr A.kXI wXr_lt A.kLens.2.2.2.2.2.2 hk

theorem pr_t : PR (FT 15) Om1Facts.t := pr_e (by norm_num)
theorem pr_ta : PR (FT 3) Om1Facts.ta := pr_e (by norm_num)
theorem pr_tb : PR (FT 252) Om1Facts.tb := pr_e (by norm_num)
theorem pr_tc : PR (FT 23) Om1Facts.tc := pr_e (by norm_num)

theorem pr_t0 : PR (A.EL.G 0) (Om1Facts.E wT0) := pr_EL (k := 0) (by norm_num)
theorem pr_i0 : PR (A.EL.G 1) (Om1Facts.E wI0) := pr_EL (k := 1) (by norm_num)
theorem pr_j0 : PR (A.EL.G 2) (Om1Facts.E wJ0) := pr_EL (k := 2) (by norm_num)
theorem pr_s1 : PR (A.EL.G 3) (Om1Facts.E wS1) := pr_EL (k := 3) (by norm_num)
theorem pr_g1 : PR (A.EL.G 4) (Om1Facts.E wG1) := pr_EL (k := 4) (by norm_num)

theorem pr_s1i : PR (A.EL.G 5) (Om1Facts.E wS1)⁻¹ := by
  have h := pr_pc pr_s1 (pr_EL (k := 5) (by norm_num))
  rw [Nat.eq_of_beq_eq_true A.kS1] at h
  have e := eq_inv_of_mul_eq_one_right (pr_eq h pr_pid)
  rw [← e]
  exact pr_EL (k := 5) (by norm_num)

theorem pr_XIinv {k : Nat} (hk : k < 7) : PR (A.XI.G k) (Om1Facts.E (wX.getD k []))⁻¹ := by
  have h := pr_pc (pr_XG hk) (pr_XI hk)
  rw [Nat.eq_of_beq_eq_true (allN_spec A.kXinv k hk)] at h
  have e := eq_inv_of_mul_eq_one_right (pr_eq h pr_pid)
  rw [← e]
  exact pr_XI hk

theorem pr_comm {P Q : Nat} {g h : Equiv.Perm (Fin 240)} (hP : PR P g) (hQ : PR Q h)
    (e : pc2 P Q = pc2 Q P) : Commute g h := by
  have h1 := pr_pc hP hQ
  rw [e] at h1
  exact pr_eq h1 (pr_pc hQ hP)

theorem cm_comm {P Q : Nat} {g h : Equiv.Perm (Fin 240)} (hP : PR P g) (hQ : PR Q h)
    (e : A.cmK P Q = true) : Commute g h := by
  unfold A.cmK at e
  exact pr_comm hP hQ (Nat.eq_of_beq_eq_true e)

theorem rel_t0 : Om1Facts.E wT0 = Om1Facts.t := by
  have h0 := pr_t0
  rw [Nat.eq_of_beq_eq_true A.kR0] at h0
  exact pr_eq h0 pr_t

theorem rel_i0 : Om1Facts.E wI0 * Om1Facts.E wI0 = Om1Facts.t := by
  have h1 := pr_pc pr_i0 pr_i0
  rw [Nat.eq_of_beq_eq_true A.kR1] at h1
  exact pr_eq h1 pr_t

theorem rel_j0 : Om1Facts.E wJ0 * Om1Facts.E wJ0 = Om1Facts.t := by
  have h2 := pr_pc pr_j0 pr_j0
  rw [Nat.eq_of_beq_eq_true A.kR2] at h2
  exact pr_eq h2 pr_t

theorem rel_ji : Om1Facts.E wJ0 * Om1Facts.E wI0 * (Om1Facts.E wJ0)⁻¹ = (Om1Facts.E wI0)⁻¹ := by
  have h3 := pr_pc pr_i0 (pr_pc pr_j0 pr_i0)
  rw [Nat.eq_of_beq_eq_true A.kR3] at h3
  have e3 := pr_eq h3 pr_j0
  rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
  exact e3

theorem rel_g1 : Om1Facts.E wG1 * Om1Facts.t * (Om1Facts.E wG1)⁻¹ = Om1Facts.t * Om1Facts.z := by
  have h4 := pr_pc pr_g1 pr_t
  rw [Nat.eq_of_beq_eq_true A.kR4] at h4
  have e4 := pr_eq h4 (pr_pc (pr_pc pr_t pr_z) pr_g1)
  rw [mul_inv_eq_iff_eq_mul]
  exact e4

theorem rel_tb : Om1Facts.tb = Om1Facts.z * Om1Facts.ta := by
  have h8 := pr_tb
  rw [Nat.eq_of_beq_eq_true A.kR8] at h8
  exact pr_eq h8 (pr_pc pr_z pr_ta)

theorem kR5a : allN 7 (fun k => A.cmK (A.TG.G k) (FT 15)) = true ∧
    A.cmK (A.EL.G 3) (FT 15) = true :=
  KernelOm2.band A.kR5

theorem rel_cT0 : ∀ w ∈ wT, Commute (Om1Facts.E w) Om1Facts.t := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := mem_getD hw
  rw [A.kLens.2.1] at hk
  exact cm_comm (pr_TG hk) pr_t (allN_spec kR5a.1 k hk)

theorem rel_cS : Commute (Om1Facts.E wS1) Om1Facts.t := cm_comm pr_s1 pr_t kR5a.2

theorem rel_cT : ∀ w ∈ wT ++ [wS1], Commute (Om1Facts.E w) Om1Facts.t := by
  intro w hw
  rcases List.mem_append.1 hw with hw | hw
  · exact rel_cT0 w hw
  · rw [List.mem_singleton] at hw
    rw [hw]
    exact rel_cS

theorem rel_cA : ∀ w ∈ wCa, Commute (Om1Facts.E w) Om1Facts.ta := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := mem_getD hw
  rw [A.kLens.2.2.1] at hk
  exact cm_comm (pr_CA hk) pr_ta (allN_spec A.kR6 k hk)

theorem rel_cC : ∀ w ∈ wCc, Commute (Om1Facts.E w) Om1Facts.tc := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := mem_getD hw
  rw [A.kLens.2.2.2.1] at hk
  exact cm_comm (pr_CC hk) pr_tc (allN_spec A.kR7 k hk)

theorem rel_fact :
    Om1Facts.E wT0 = Om1Facts.t ∧ Om1Facts.E wI0 * Om1Facts.E wI0 = Om1Facts.t ∧
      Om1Facts.E wJ0 * Om1Facts.E wJ0 = Om1Facts.t ∧
      Om1Facts.E wJ0 * Om1Facts.E wI0 * (Om1Facts.E wJ0)⁻¹ = (Om1Facts.E wI0)⁻¹ ∧
      Om1Facts.E wG1 * Om1Facts.t * (Om1Facts.E wG1)⁻¹ = Om1Facts.t * Om1Facts.z ∧
      (∀ w ∈ wT ++ [wS1], Commute (Om1Facts.E w) Om1Facts.t) ∧
      (∀ w ∈ wCa, Commute (Om1Facts.E w) Om1Facts.ta) ∧
      (∀ w ∈ wCc, Commute (Om1Facts.E w) Om1Facts.tc) ∧ Om1Facts.tb = Om1Facts.z * Om1Facts.ta :=
  ⟨rel_t0, rel_i0, rel_j0, rel_ji, rel_g1, rel_cT, rel_cA, rel_cC, rel_tb⟩

theorem G_eq (ws : List (List Nat)) :
    Om1Facts.G ws = Subgroup.closure (permsA 240 (wsA (reflTab ()) ws)) := by
  unfold Om1Facts.G
  congr 1
  ext x
  simp only [permsA, wsA, Set.mem_image, Set.mem_setOf_eq, List.size_toArray, List.length_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    refine ⟨k, hk, ?_⟩
    rw [getElem!_pos _ k (by simpa using hk)]
    simp [Om1Facts.E]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨ws[k], List.getElem_mem hk, ?_⟩
    rw [getElem!_pos _ k (by simpa using hk)]
    simp [Om1Facts.E]

theorem keyPts_lt : ∀ p ∈ keyPtsA.toList, p < 240 := by decide +kernel

@[expose] def EnumR (ws : List (List Nat)) (T : Nat → Nat) (sz : Nat) : Prop :=
  Nat.card (Om1Facts.G ws) = sz ∧ (∀ i < sz, PR (T i) (permOfArr 240 (unpack 240 8 (T i)))) ∧
    (∀ i < sz, permOfArr 240 (unpack 240 8 (T i)) ∈ Om1Facts.G ws) ∧
    ∀ x ∈ Om1Facts.G ws, ∃ i < sz, PR (T i) x

theorem enum_pr {ws : List (List Nat)} {ng N sz : Nat} {G T E S : Nat → Nat} {SK : List Nat}
    (hlt : ∀ w ∈ ws, ∀ r ∈ w, r < 240) (hlen : ws.length = ng)
    (hG : allN ng (A.genOK ws G) = true) (hk : bfsK 240 8 ng G N T E S = true)
    (hK : keysSK 240 8 keyPtsA.toList N T SK = true) (hN : N = sz) : EnumR ws T sz := by
  subst hN
  have hg1 : ∀ k < ng, Nat.beq (G k) (wAK (ws.getD k [])) = true ∧ A.okK2 (G k) = true :=
    fun k hk => KernelOm2.band (allN_spec hG k hk)
  have hs : (wsA (reflTab ()) ws).size = ng := by simp [wsA, hlen]
  have hgs : ∀ k < ng, (wsA (reflTab ()) ws)[k]! = unpack 240 8 (G k) := by
    intro k hk
    rw [getElem!_pos _ k (by rw [hs]; exact hk)]
    simp only [wsA, List.getElem_toArray, List.getElem_map]
    rw [← List.getD_eq_getElem _ [] (by omega), Nat.eq_of_beq_eq_true (hg1 k hk).1]
    exact (KernelOm2.wA_eq _ (hlt _ (getD_mem (by omega)))).1
  have hp : ∀ k < ng, permOK 240 8 (mask 8) (240 * 8) (G k) (pinvS 240 8 (mask 8) (G k)) =
      true := fun k hk => by
    have h := (hg1 k hk).2
    unfold A.okK2 at h
    exact (KernelOm2.band (KernelOm2.band h).2).1
  have hok := enumOK_of_bfsK_base (fuel := N) hs hgs hp hk keyPts_lt hK le_rfl
  have hpts := enumBfs_pts_base (fuel := N) hs hgs hk keyPts_lt hK le_rfl
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec keyPts_lt hok
  have hsz : (enumBfs 240 (wsA (reflTab ()) ws) keyPtsA.toList N).pts.size = N := by
    rw [hpts, Array.size_ofFn]
  have hget : ∀ i < N, (enumBfs 240 (wsA (reflTab ()) ws) keyPtsA.toList N).pts[i]! =
      unpack 240 8 (T i) := by
    intro i hi
    rw [getElem!_pos _ i (by rw [hsz]; exact hi)]
    simp only [hpts, Array.getElem_ofFn]
  have hv : ∀ i < N, PR (T i) (permOfArr 240 (unpack 240 8 (T i))) := fun i hi => by
    have := hval i (by rw [hsz]; exact hi)
    rw [hget i hi] at this
    exact prep_of_rep (rep_of_validA this)
  refine ⟨by rw [G_eq, hcard, hsz], hv, fun i hi => ?_, fun x hx => ?_⟩
  · rw [G_eq, hmem]
    exact ⟨i, by rw [hsz]; exact hi, by rw [hget i hi]⟩
  rw [G_eq] at hx
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
  rw [hsz] at hi
  rw [hget i hi]
  exact ⟨i, hi, hv i hi⟩

theorem okE0 : bfsK 240 8 E0.ng E0.G E0.N E0.T E0.E E0.S = true :=
  bfsK_of_slices (L := 64) (K := 64) (C := E0.C) (by decide) (by norm_num) A.kSz E0.g E0.csAll
    E0.t0 E0.dist (Nat.eq_of_beq_eq_true E0.c0) (Nat.eq_of_beq_eq_true E0.cK) E0.rsAll

theorem okE1 : bfsK 240 8 E1.ng E1.G E1.N E1.T E1.E E1.S = true :=
  bfsK_of_slices (L := 27) (K := 1) (C := E1.C) (by decide) (by norm_num) A.kSz E1.g E1.csAll
    E1.t0 E1.dist (Nat.eq_of_beq_eq_true E1.c0) (Nat.eq_of_beq_eq_true E1.cK) E1.rsAll

theorem okEa : bfsK 240 8 Ea.ng Ea.G Ea.N Ea.T Ea.E Ea.S = true :=
  bfsK_of_slices (L := 64) (K := 32) (C := Ea.C) (by decide) (by norm_num) A.kSz Ea.g Ea.csAll
    Ea.t0 Ea.dist (Nat.eq_of_beq_eq_true Ea.c0) (Nat.eq_of_beq_eq_true Ea.cK) Ea.rsAll

theorem okEa3 : bfsK 240 8 Ea3.ng Ea3.G Ea3.N Ea3.T Ea3.E Ea3.S = true :=
  bfsK_of_slices (L := 9) (K := 1) (C := Ea3.C) (by decide) (by norm_num) A.kSz Ea3.g Ea3.csAll
    Ea3.t0 Ea3.dist (Nat.eq_of_beq_eq_true Ea3.c0) (Nat.eq_of_beq_eq_true Ea3.cK) Ea3.rsAll

theorem okEa5 : bfsK 240 8 Ea5.ng Ea5.G Ea5.N Ea5.T Ea5.E Ea5.S = true :=
  bfsK_of_slices (L := 5) (K := 1) (C := Ea5.C) (by decide) (by norm_num) A.kSz Ea5.g Ea5.csAll
    Ea5.t0 Ea5.dist (Nat.eq_of_beq_eq_true Ea5.c0) (Nat.eq_of_beq_eq_true Ea5.cK) Ea5.rsAll

theorem okEc : bfsK 240 8 Ec.ng Ec.G Ec.N Ec.T Ec.E Ec.S = true :=
  bfsK_of_slices (L := 64) (K := 16) (C := Ec.C) (by decide) (by norm_num) A.kSz Ec.g Ec.csAll
    Ec.t0 Ec.dist (Nat.eq_of_beq_eq_true Ec.c0) (Nat.eq_of_beq_eq_true Ec.cK) Ec.rsAll

theorem okEpc : bfsK 240 8 Epc.ng Epc.G Epc.N Epc.T Epc.E Epc.S = true :=
  bfsK_of_slices (L := 3) (K := 1) (C := Epc.C) (by decide) (by norm_num) A.kSz Epc.g Epc.csAll
    Epc.t0 Epc.dist (Nat.eq_of_beq_eq_true Epc.c0) (Nat.eq_of_beq_eq_true Epc.cK) Epc.rsAll

theorem okEK : bfsK 240 8 EK.ng EK.G EK.N EK.T EK.E EK.S = true :=
  bfsK_of_slices (L := 32) (K := 1) (C := EK.C) (by decide) (by norm_num) A.kSz EK.g EK.csAll
    EK.t0 EK.dist (Nat.eq_of_beq_eq_true EK.c0) (Nat.eq_of_beq_eq_true EK.cK) EK.rsAll

theorem wS0_lt : ∀ w ∈ wS0, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wP3_lt : ∀ w ∈ wP3, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wSa_lt : ∀ w ∈ wSa, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wPa3_lt : ∀ w ∈ wPa3, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wPa5_lt : ∀ w ∈ wPa5, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wSc_lt : ∀ w ∈ wSc, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem wPc_lt : ∀ w ∈ wPc, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)
theorem k0W_lt : ∀ w ∈ A.k0W, ∀ r ∈ w, r < 240 := lt_of_sub (by decide +kernel)

theorem enum0 : EnumR wS0 E0.T 4096 :=
  enum_pr wS0_lt A.kLen.1 A.kEG0 okE0 E0.keys A.kN.1
theorem enum1 : EnumR wP3 E1.T 27 :=
  enum_pr wP3_lt A.kLen.2.1 A.kEG1 okE1 E1.keys A.kN.2.1
theorem enuma : EnumR wSa Ea.T 2048 :=
  enum_pr wSa_lt A.kLen.2.2.1 A.kEGa okEa Ea.keys A.kN.2.2.1
theorem enuma3 : EnumR wPa3 Ea3.T 9 :=
  enum_pr wPa3_lt A.kLen.2.2.2.1 A.kEGa3 okEa3 Ea3.keys A.kN.2.2.2.1
theorem enuma5 : EnumR wPa5 Ea5.T 5 :=
  enum_pr wPa5_lt A.kLen.2.2.2.2.1 A.kEGa5 okEa5 Ea5.keys A.kN.2.2.2.2.1
theorem enumc : EnumR wSc Ec.T 1024 :=
  enum_pr wSc_lt A.kLen.2.2.2.2.2.1 A.kEGc okEc Ec.keys A.kN.2.2.2.2.2.1
theorem enumpc : EnumR wPc Epc.T 3 :=
  enum_pr wPc_lt A.kLen.2.2.2.2.2.2.1 A.kEGpc okEpc Epc.keys A.kN.2.2.2.2.2.2.1
theorem enumK : EnumR A.k0W EK.T 32 :=
  enum_pr k0W_lt A.kLen.2.2.2.2.2.2.2 A.kEGK okEK EK.keys A.kN.2.2.2.2.2.2.2

theorem enum_fact :
    Nat.card (Om1Facts.G wS0) = 4096 ∧ Nat.card (Om1Facts.G wP3) = 27 ∧
      Nat.card (Om1Facts.G wSa) = 2048 ∧ Nat.card (Om1Facts.G wPa3) = 9 ∧
      Nat.card (Om1Facts.G wPa5) = 5 ∧ Nat.card (Om1Facts.G wSc) = 1024 ∧
      Nat.card (Om1Facts.G wPc) = 3 :=
  ⟨enum0.1, enum1.1, enuma.1, enuma3.1, enuma5.1, enumc.1, enumpc.1⟩

theorem maskOK_all : ∀ j < 126, A.maskOK j = true := by
  intro j hj
  have hc : ∀ c < 9, A.maskOKc c = true := by
    intro c hc
    interval_cases c
    exacts [A.maskOKc0, A.maskOKc1, A.maskOKc2, A.maskOKc3, A.maskOKc4, A.maskOKc5, A.maskOKc6,
      A.maskOKc7, A.maskOKc8]
  have h := allN_spec (hc (j / 14) (by omega)) (j % 14) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 14 (j / 14)) (j % 14) = j := Nat.div_add_mod j 14
  rw [e] at h
  exact h

theorem mask_lt : ∀ d ∈ maskData, d.1 < 256 ∧ ∀ r ∈ d.2.2, r < 240 := by decide +kernel

theorem rep_lt : ∀ i < 4, repMasks.getD i 0 < 256 := by decide

theorem mask_fact : ∀ d ∈ maskData, d.2.1 < 4 ∧
    Om1Facts.E d.2.2 * Om1Facts.e d.1 * (Om1Facts.E d.2.2)⁻¹ =
      Om1Facts.e (repMasks.getD d.2.1 0) := by
  intro d hd
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hd
  have hg : maskData.getD j (0, 0, []) = d := by rw [List.getD_eq_getElem _ _ hj, e]
  have h := maskOK_all j (by rw [A.kMaskLen] at hj; exact hj)
  unfold A.maskOK at h
  simp only [hg] at h
  obtain ⟨h1, h2⟩ := KernelOm2.band h
  have hi : d.2.1 < 4 := Nat.blt_eq.mp h1
  rw [strictB_eq] at h2
  obtain ⟨hm, hw⟩ := mask_lt d hd
  have p := pr_pc (pr_E hw) (pr_e hm)
  rw [Nat.eq_of_beq_eq_true h2] at p
  have e2 := pr_eq p (pr_pc (pr_e (rep_lt _ hi)) (pr_E hw))
  refine ⟨hi, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact e2

theorem ncard_le_of_pr {s : Set (Equiv.Perm (Fin 240))} {L : List Nat} {T : Nat → Nat}
    (h : ∀ x ∈ s, ∃ i ∈ L, PR (T i) x) : s.ncard ≤ L.length := by
  have hsub : s ⊆ (fun i => permOfArr 240 (unpack 240 8 (T i))) '' (L.toFinset : Set Nat) := by
    intro x hx
    obtain ⟨i, hi, hp⟩ := h x hx
    refine ⟨i, by simpa using hi, ?_⟩
    exact permOfArr_eq_of_rep (rep_unpack hp)
  calc s.ncard
      ≤ ((fun i => permOfArr 240 (unpack 240 8 (T i))) '' (L.toFinset : Set Nat)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (L.toFinset : Set Nat).ncard := Set.ncard_image_le L.toFinset.finite_toSet
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le _

theorem r0L_pr : ∀ a ∈ A.r0L, ∃ g ∈ Om1Facts.R, PR a g := by
  have ha : Om1Facts.E wI0 ∈ Om1Facts.R := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : Om1Facts.E wJ0 ∈ Om1Facts.R := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have p11 := pr_pc pr_i0 pr_i0
  have p111 := pr_pc p11 pr_i0
  have m11 := Om1Facts.R.mul_mem ha ha
  have m111 := Om1Facts.R.mul_mem m11 ha
  intro a h
  simp only [A.r0L, A.q8L, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Om1Facts.R.one_mem, pr_pid⟩
  · exact ⟨_, ha, pr_i0⟩
  · exact ⟨_, m11, p11⟩
  · exact ⟨_, m111, p111⟩
  · exact ⟨_, hb, pr_j0⟩
  · exact ⟨_, Om1Facts.R.mul_mem hb ha, pr_pc pr_j0 pr_i0⟩
  · exact ⟨_, Om1Facts.R.mul_mem hb m11, pr_pc pr_j0 p11⟩
  · exact ⟨_, Om1Facts.R.mul_mem hb m111, pr_pc pr_j0 p111⟩

theorem r0_fact : Nat.card Om1Facts.R ≤ 8 := by
  have hQa := A.kQa
  have hQb := A.kQb
  simp only [List.all_eq_true, List.any_eq_true, strictB_eq] at hQa hQb
  have hpr : ∀ {a : Nat} {g : Equiv.Perm (Fin 240)}, a ∈ A.r0L → PR a g → ∀ {b : Nat}
      {h : Equiv.Perm (Fin 240)}, b ∈ A.r0L → PR b h → ∃ c ∈ A.r0L, PR c (g * h) := by
    intro a g ha pg b h hb ph
    obtain ⟨c, hc, e⟩ := hQa a ha b hb
    exact ⟨c, hc, by rw [← Nat.eq_of_beq_eq_true e]; exact pr_pc pg ph⟩
  have hsub : ∀ x ∈ Om1Facts.R, ∃ a ∈ A.r0L, PR a x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨A.EL.G 1, by simp [A.r0L, A.q8L], pr_i0⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨A.EL.G 2, by simp [A.r0L, A.q8L], pr_j0⟩
    | one => exact ⟨pidn 240 8, by simp [A.r0L, A.q8L, A.pid1], pr_pid⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, pa⟩ := hx
      obtain ⟨b, hb, pb⟩ := hy
      exact hpr ha pa hb pb
    | inv x _ hx =>
      obtain ⟨a, ha, pa⟩ := hx
      obtain ⟨b, hb, e⟩ := hQb a ha
      obtain ⟨h, -, pb⟩ := r0L_pr b hb
      have p := pr_pc pa pb
      rw [Nat.eq_of_beq_eq_true e] at p
      have e2 := eq_inv_of_mul_eq_one_right (pr_eq p pr_pid)
      exact ⟨b, hb, by rw [← e2]; exact pb⟩
  have e : Nat.card Om1Facts.R = (Om1Facts.R : Set (Equiv.Perm (Fin 240))).ncard :=
    (Nat.card_coe_set_eq _).symm
  rw [e]
  have := ncard_le_of_pr (T := id) (L := A.r0L) (s := (Om1Facts.R : Set (Equiv.Perm (Fin 240))))
    (fun x hx => hsub x hx)
  exact this.trans (by simp [A.r0L, A.q8L])

end CertificateChecks.KernelOm1

end
