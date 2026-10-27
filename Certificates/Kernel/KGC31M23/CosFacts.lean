
module

public import Certificates.Kernel.KGC31M23.CosGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M23
open CertificateChecks.KernelSporSch CFSG.KC.CosetConj

theorem kEbP : pebasis 23 5 wP = true ∧ pebasis 23 5 tP = true ∧ pebasis 23 5 eP = true ∧
    pebasis 23 5 sP = true := by
  have h := kEb
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨a, b, c, d⟩

theorem ebW (ws : List (List ℤ)) :
    ebasisOK 23 (ws.map (wordT 23 gensT)) = pebasis 23 5 (ws.map pw) := by
  rw [mapW]
  exact ebasisOK_tabP hsz (ppL ws)

theorem eb : ebasisOK 23 wT = true ∧ ebasisOK 23 tT = true ∧ ebasisOK 23 eT = true ∧
    ebasisOK 23 sT = true := by
  obtain ⟨a, b, c, d⟩ := kEbP
  exact ⟨(ebW wW).trans a, (ebW tW).trans b, (ebW eW).trans c, (ebW sW).trans d⟩

theorem cntC (ws : List (List ℤ)) :
    cbT.countP (commAll 23 (ws.map (wordT 23 gensT))) = CB.countP (pcommAll 23 5 (ws.map pw)) := by
  rw [countP_cbT, mapW]
  exact List.countP_congr fun c hc => by rw [commAll_tabP (ppL ws) (ppCB c hc)]

theorem cnt : cbT.countP (commAll 23 wT) = 16 ∧ cbT.countP (commAll 23 tT) = 16 ∧
    cbT.countP (commAll 23 eT) = 8 ∧ cbT.countP (commAll 23 sT) = 16 := by
  have h := kCm
  unfold wP tP eP sP at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [wT, cntC, ← Nat.eq_of_beq_eq_true a]
  · rw [tT, cntC, ← Nat.eq_of_beq_eq_true b]
  · rw [eT, cntC, ← Nat.eq_of_beq_eq_true c]
  · rw [sT, cntC, ← Nat.eq_of_beq_eq_true d]

theorem cntN (ws : List (List ℤ)) : cbT.countP (normAll 23 (ws.map (wordT 23 gensT))) =
    CB.countP fun c => pnormAll 23 5 (ws.map pw) c (pinv 23 5 c) := by
  rw [countP_cbT, mapW]
  exact List.countP_congr fun c hc => by rw [normAll_tabP hsz (ppL ws) (ppCB c hc)]

theorem normAll_mul {ws : List (List ℤ)} (hE : EBasis (bv ws)) {v : List ℤ}
    (hv : ev v ∈ eNorm hE) (g : Equiv.Perm (Fin 23)) :
    normAll 23 (ws.map (wordT 23 gensT)) (toTable (ev v * g)) =
      normAll 23 (ws.map (wordT 23 gensT)) (toTable g) := by
  rw [Bool.eq_iff_iff, normAll_eq ws hE (rep_toTable hn23 _), normAll_eq ws hE (rep_toTable hn23 _)]
  exact Subgroup.mul_mem_cancel_left _ hv

theorem cos_w : cosetCount 23 cbT wCosetT (normAll 23 wT) = 40320 := by
  have hE := eb_of kEbP.1
  have hN := kNW
  unfold wP at hN
  rw [wCosetT, wT, cosetCount_eq fun m hm => ?_, cntN wW, Nat.eq_of_beq_eq_true hN]
  · rfl
  have hm' : m < 15 := hm
  have hR := List.all_eq_true.1 kRW m (List.mem_range.2 hm')
  unfold wP rW at hR
  have hv := mem_eNorm_of hE (v := wCosetW.getD m []) hR
  rw [List.getD_eq_getElem _ _ hm] at hv
  refine countP_coset (by rw [inv_mul_cancel]; exact C.one_mem) fun g _ => normAll_mul hE hv g

theorem cos_t : cosetCount 23 cbT tCosetT (fun g => normAll 23 tT g && fixesAll g triT) = 960 := by
  have hE := eb_of kEbP.2.1
  have hc : cbT.countP (fun g => normAll 23 (tW.map (wordT 23 gensT)) g && fixesAll g triT) =
      CB.countP fT := by
    rw [countP_cbT]
    exact List.countP_congr fun c hc => by
      rw [mapW, normAll_tabP hsz (ppL tW) (ppCB c hc), fix_tabP (ppCB c hc), fT, tP]
  rw [tCosetT, tT, cosetCount_eq fun m hm => ?_, hc, Nat.eq_of_beq_eq_true kNU]
  · rfl
  have hm' : m < 15 := hm
  have h := List.all_eq_true.1 kNT m (List.mem_range.2 hm')
  unfold tP nTP at h
  simp only [conjOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [rT, List.getD_eq_getElem _ _ hm] at h1
  have hv := mem_eNorm_of hE h2
  have hfix : ∀ i : Fin 23, i.val ∈ triT → ev (wI (CFSG.KD.M23Conj.nT.getD m [])) i = i :=
    (fixesAll_iff htri (rep_pw _)).1 (by rw [fix_tabP (ppw' _)]; exact h3)
  refine countP_coset (f := fun g => normAll 23 (tW.map (wordT 23 gensT)) g && fixesAll g triT)
    (w := tCosetW[m]) (kappa_mem (conj_eq_of h1)) fun g _ => ?_
  rw [fix_mul hfix g, normAll_mul hE hv g]

theorem cos_e : cosetCount 23 cbT eCosetT (normAll 23 eT) = 1344 := by
  have hE := eb_of kEbP.2.2.1
  have hN := kNEc
  unfold eP at hN
  rw [eCosetT, eT, cosetCount_eq fun m hm => ?_, cntN eW, Nat.eq_of_beq_eq_true hN]
  · rfl
  have hm' : m < 7 := hm
  have h := List.all_eq_true.1 kNE m (List.mem_range.2 hm')
  unfold eP nEP at h
  simp only [conjOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [rE, List.getD_eq_getElem _ _ hm] at h1
  have hv := mem_eNorm_of hE h2
  exact countP_coset (kappa_mem (conj_eq_of h1)) fun g _ => normAll_mul hE hv g

end CertificateChecks.KernelKGC31M23

end
