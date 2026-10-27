module

public import Certificates.Kernel.FiveStd.WGlue3
public import Certificates.Kernel.FiveStd.WChk4

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

theorem eqL_code (L M : List E) : eqL L M = eqLK (L.map codeE) (M.map codeE) := by
  unfold eqL subL eqLK
  simp only [List.all_map, Function.comp_def, inL_codeE]

theorem hInv_code (a b g g2 h : E) :
    (h == oneE || (!(normAll [a, b] [h] (powers h 5)) || eqL (powers h 5) (powers g 5) ||
      eqL (powers h 5) (powers g2 5))) =
      hInvK (codeE a) (codeE b) (codeE g) (codeE g2) (codeE h) := by
  unfold hInvK
  rw [beq_code, codeE_oneE, normAll_code, eqL_code, eqL_code]
  simp only [List.map_cons, List.map_nil, map_powers, Bool.or_assoc]

theorem goodX1_of {t u a b g : E}
    (h5 : eqL (Cs.filter fun c => normG c [conjE t g] (powers (conjE t g) 5))
      (prod3 (powers (conjE t g) 5) K1l (ppE a b 4 4)) = true)
    (h6 : eqL (Cs.filter fun c => cenG c [conjE t g]) (prod2 (powers (conjE t g) 5) K1l) = true)
    (h7 : eqL (Cs.filter fun c => normG c [g, conjE t g] (ppE g (conjE t g) 5 5))
      (prod3 (ppE g (conjE t g) 5 5) (ppE a b 4 4) [oneE, t]) = true)
    (hr : gRestK (codeE t) (codeE u) (codeE a) (codeE b) (codeE g) = true) :
    goodX1 t u a b (ppE a b 4 4) g = true := by
  unfold gRestK at hr
  rw [letB_eq, ← conj_code t g, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r8⟩, r9⟩ := hr
  have hX : (ppE g (conjE t g) 5 5).all (fun h => h == oneE ||
      (!(normAll [a, b] [h] (powers h 5)) || eqL (powers h 5) (powers g 5) ||
        eqL (powers h 5) (powers (conjE t g) 5))) = true := by
    rw [List.all_eq_true]
    intro h hh
    have hm : codeE h ∈ ppK (codeE g) (codeE (conjE t g)) 5 5 := by
      rw [← map_ppE]
      exact List.mem_map_of_mem hh
    have key : hInvK (codeE a) (codeE b) (codeE g) (codeE (conjE t g)) (codeE h) = true :=
      List.all_eq_true.1 r8 (codeE h) hm
    rw [← hInv_code] at key
    exact key
  unfold goodX1
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, h5⟩, h6⟩, h7⟩, hX⟩, ?_⟩
  · rw [normAll_code]
    simp only [List.map_cons, List.map_nil, map_powers]
    exact r1
  · rw [beq_code, codeE_invE, conj_code]
    exact r2
  · rw [commE_codeE]
    exact r3
  · rw [nodupL_codeE, map_ppE]
    exact of_decide_eq_true r4
  · rw [beq_iff_eq] at r9 ⊢
    rw [← List.length_map (f := codeE),
      map_filter_codeE _ _ (fun x => Nat.beq (mulK x (codeE t)) (mulK (codeE t) x))
        (fun x => commE_codeE x t), map_ppE]
    exact r9

end CertificateChecks.FiveStd

end
