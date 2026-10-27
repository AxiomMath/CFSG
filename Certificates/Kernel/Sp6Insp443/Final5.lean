module

public import Certificates.Kernel.Sp6Insp443.SubChk5
public import Certificates.Kernel.Sp6Insp443.Count5
public import Certificates.Kernel.Sp6Insp443.Final7
public import CFSG.Certificates.Kernel.Sp6Insp443.SixESound

public section

namespace CertificateChecks.KernelS6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Sp6I CFSG.KC.KGC31P CFSG.KC.BfsPin
  CFSG.SectionRank.QTK.Insp443.Sp6 CFSG.SectionRank.QTK.Insp443.PermKit.Native
  CFSG.Quasithin.KGC31.Native CFSG.Sporadic.Th.Native CertificateChecks.KernelSpor
  CFSG.Sporadic.Schreier
open CFSG.KC.Child3 (tabP)

theorem siftOK_of {T : CFSG.Sporadic.Th.Native.Table} (h : tabK 36 6 T = true)
    (hs : Co3Sp36.sift (packT 6 T) = true) : siftOK T = true := by
  obtain ⟨-, hp⟩ := tabK_spec sz36 h
  unfold tabK at h
  rw [Orb.strictB_eq, Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hsz, ht, -⟩ := h
  have hc := hp.1
  unfold canonK at hc
  rw [Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨-, hshr, hr⟩ := hc
  have harr := map_toNat_of_tabPK (Nat.eq_of_beq_eq_true hsz) ht
  unfold siftOK CFSG.Sporadic.Schreier.Co3.co3Sp36Levels
  exact siftK_soundR Co3Sp36.binds Co3Sp36.perm Co3Sp36.hl harr (Nat.eq_of_beq_eq_true hshr) hr hs

theorem cand5 {k : Nat} (hk : k < 6) :
    cands5.getD k [] = ((cands5.getD k []).map (packT 6)).map (tabP 36 6) ∧
      ∀ a ∈ (cands5.getD k []).map (packT 6), PP 36 6 a := by
  have hl : k < cands5.length := hk
  refine tabsK_spec sz36 (List.all_eq_true.mp ch725106k5 _ ?_)
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_mem _

theorem tabsAll {L : List (List CFSG.Sporadic.Th.Native.Table)}
    (h : (L.all fun Ts => tabsK 36 6 Ts) = true) :
    L = (L.map (List.map (packT 6))).map (List.map (tabP 36 6)) ∧
      ∀ D ∈ L.map (List.map (packT 6)), ∀ a ∈ D, PP 36 6 a := by
  refine ⟨?_, fun D hD => ?_⟩
  · rw [List.map_map]
    conv_lhs => rw [← List.map_id L]
    refine List.map_congr_left fun Ts hT => ?_
    exact (tabsK_spec sz36 (List.all_eq_true.mp h Ts hT)).1
  · obtain ⟨Ts, hT, rfl⟩ := List.mem_map.mp hD
    exact (tabsK_spec sz36 (List.all_eq_true.mp h Ts hT)).2

theorem tab1 {T : CFSG.Sporadic.Th.Native.Table} {Ts : List CFSG.Sporadic.Th.Native.Table}
    (hT : T ∈ Ts) (h : tabsK 36 6 Ts = true) : tabK 36 6 T = true := by
  induction Ts with
  | nil => exact absurd hT List.not_mem_nil
  | cons U Us ih =>
    have h' : bAnd(tabK 36 6 U, tabsK 36 6 Us) = true := h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hT with rfl | hT
    · exact h'.1
    · exact ih hT h'.2

theorem tabOf {T : CFSG.Sporadic.Th.Native.Table} (h : tabK 36 6 T = true) :
    T = tabP 36 6 (packT 6 T) ∧ PP 36 6 (packT 6 T) := tabK_spec sz36 h

theorem sub5 {k j : Nat} (hk : k < 6) (hj : j < 6)
    (h : psubOK 36 6 ((cands5.getD k []).map (packT 6)) ((cands5.getD j []).map (packT 6)) = true) :
    subOK 36 (cands5.getD k []) (cands5.getD j []) = true := by
  obtain ⟨e1, p1⟩ := cand5 hk
  obtain ⟨e2, p2⟩ := cand5 hj
  exact (congrArg₂ (subOK 36) e1 e2).trans ((subOK_tabP sz36 p1 p2).trans h)

theorem spanEq5 {k : Nat} (hk : k < 6) {ds : List (List CFSG.Sporadic.Th.Native.Table)}
    (hd : (ds.all fun Ts => tabsK 36 6 Ts) = true)
    (h : pspanEq 36 6 ((cands5.getD k []).map (packT 6)) ((ds.getD 0 []).map (packT 6)) = true) :
    spanEq 36 (cands5.getD k []) (ds.getD 0 []) = true := by
  obtain ⟨e1, p1⟩ := cand5 hk
  obtain ⟨e2, p2⟩ := tabsAll hd
  have e3 : ds.getD 0 [] = ((ds.getD 0 []).map (packT 6)).map (tabP 36 6) := by
    conv_lhs => rw [e2]
    rw [getD_mapL, getD_mapL]
  have p3 : ∀ a ∈ (ds.getD 0 []).map (packT 6), PP 36 6 a := by
    rw [← getD_mapL]
    exact PP_getD p2 0
  exact (congrArg₂ (spanEq 36) e1 e3).trans ((spanEq_tabP sz36 p1 p3).trans h)

theorem six5 {k : Nat} (hk : k < 6) {ds : List (List CFSG.Sporadic.Th.Native.Table)}
    {hs : List CFSG.Sporadic.Th.Native.Table} {a g h : CFSG.Sporadic.Th.Native.Table}
    (hd : (ds.all fun Ts => tabsK 36 6 Ts) = true) (hdl : ds.length = 6)
    (hh : tabsK 36 6 hs = true) (hagh : tabsK 36 6 [a, g, h] = true)
    (hc : psixE 36 6 ((cands5.getD k []).map (packT 6)) (ds.map (List.map (packT 6)))
      (hs.map (packT 6)) (packT 6 a) (packT 6 g) (packT 6 h) = true) :
    sixCheckE 36 (cands5.getD k []) ds hs a g h = true := by
  obtain ⟨e1, p1⟩ := cand5 hk
  obtain ⟨e2, p2⟩ := tabsAll hd
  obtain ⟨e3, p3⟩ := tabsK_spec sz36 hh
  obtain ⟨ea, pa⟩ := tabOf (tab1 (List.mem_cons_self) hagh)
  obtain ⟨eg, pg⟩ := tabOf (tab1 (List.mem_cons_of_mem _ List.mem_cons_self) hagh)
  obtain ⟨eh, ph⟩ := tabOf (tab1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)) hagh)
  have key := sixCheckE_tabP sz36 p1 p2 p3 pa pg ph (by rw [List.length_map, hdl])
  have tr : ∀ W D H A G K, W = ((cands5.getD k []).map (packT 6)).map (tabP 36 6) →
      D = (ds.map (List.map (packT 6))).map (List.map (tabP 36 6)) →
      H = (hs.map (packT 6)).map (tabP 36 6) → A = tabP 36 6 (packT 6 a) →
      G = tabP 36 6 (packT 6 g) → K = tabP 36 6 (packT 6 h) → sixCheckE 36 W D H A G K = true := by
    rintro _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    exact key.trans hc
  exact tr _ _ _ _ _ _ e1 e2 e3 ea eg eh

theorem chkP5_true :
    chkP5 () = true := by
  obtain ⟨b0, b1, b2, b3, b4, b5, s0, s2, s5⟩ := ch725106b
  obtain ⟨d1, d3, d4⟩ := ch725106kd
  obtain ⟨k1, k3, k4, t1, t3, t4⟩ := ch725106kh
  have hf := List.all_eq_true.mp ch725106f
  have sf : ∀ (T : CFSG.Sporadic.Th.Native.Table) (Ts : List CFSG.Sporadic.Th.Native.Table),
      T ∈ Ts → tabsK 36 6 Ts = true →
      T ∈ [a1T, g1T, h1T, a3T, g3T, h3T, a4T, g4T, h4T] → siftOK T = true :=
    fun T Ts h1 h2 h3 => siftOK_of (tab1 h1 h2) (hf T h3)
  unfold chkP5
  simp only []
  rw [six5 (by norm_num) d1 rfl k1 t1 ch725106e1, six5 (by norm_num) d3 rfl k3 t3 ch725106e3,
    six5 (by norm_num) d4 rfl k4 t4 ch725106e4,
    sf a1T _ (by simp) t1 (by simp), sf g1T _ (by simp) t1 (by simp),
    sf h1T _ (by simp) t1 (by simp), sf a3T _ (by simp) t3 (by simp),
    sf g3T _ (by simp) t3 (by simp), sf h3T _ (by simp) t3 (by simp),
    sf a4T _ (by simp) t4 (by simp), sf g4T _ (by simp) t4 (by simp),
    sf h4T _ (by simp) t4 (by simp),
    sub5 (by norm_num) (by norm_num) b0, sub5 (by norm_num) (by norm_num) b1,
    sub5 (by norm_num) (by norm_num) b2, sub5 (by norm_num) (by norm_num) b3,
    sub5 (by norm_num) (by norm_num) b4, sub5 (by norm_num) (by norm_num) b5,
    spanEq5 (by norm_num) d1 s0, spanEq5 (by norm_num) d3 s2, spanEq5 (by norm_num) d4 s5, count5]
  rfl

end CertificateChecks.KernelS6I

end
