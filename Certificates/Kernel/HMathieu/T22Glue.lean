
module

public import Certificates.Kernel.HMathieu.T22
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import CFSG.Quasithin.Background.HFCodeInputs

public section

namespace CertificateChecks.KernelHMathieu.T22

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu

theorem t22_eq : T22s2 = PT.ofGens 24 (gens.map unpk) 64 := by
  unfold T22s2 gens22s2
  congr 1

theorem packed : Packed T22s2 E where
  elems := by
    rw [t22_eq]
    change bfsClosure 24 (gens.map unpk) 64 = _
    rw [bfsClosure_eq (List.all_eq_true.1 vpG), bfs]
  one := by rw [t22_eq]; rfl
  vp := List.all_eq_true.1 vpE

theorem invData : InvData T22s2 E inv P :=
  ⟨by rw [invols_idx packed, invOK], pOK⟩

theorem len : inv22s2.length = 71 := by
  rw [inv22s2, length_invols invData, lenOK.1]

theorem gtabs : GTabs inv22s2 (cmD rows) (mkD rows) :=
  gtabs_of packed invData (by rw [lenOK.1]; exact tabs)

theorem lenP : P.length = 72 := by rw [pOK]; simp [lenOK.1]

theorem idOK : E.getD 0 0 = pidn 24 5 := by decide +kernel

theorem act_el {k : Nat} (hk : k ≤ 71) :
    act22s2 (el inv22s2 k) = actM (Mc.getD k []) := by
  funext m
  have e := map_elems_get packed (fun a => matOf 10 (act10 a)) (el inv22s2 k)
  unfold act22s2 mats22s2 matsOf10
  have hk' : k ≤ T22s2.invols.length := by rw [← inv22s2, len]; exact hk
  rw [e, show inv22s2 = T22s2.invols from rfl, pk_el packed invData hk', mcOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [lenP]; omega) _ 0]
  unfold matP
  congr 1

theorem actC_el {k : Nat} (hk : k ≤ 71) :
    (fun m => actM (matsC22[(el inv22s2 k).idx]!) m) = actM (Md.getD k []) := by
  funext m
  have e := map_elems_get packed (fun a => matOf 10 (actC10 a)) (el inv22s2 k)
  unfold matsC22 matsOfC10
  have hk' : k ≤ T22s2.invols.length := by rw [← inv22s2, len]; exact hk
  rw [e, show inv22s2 = T22s2.invols from rfl, pk_el packed invData hk', mdOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [lenP]; omega) _ 0]
  unfold matP
  congr 1

theorem codeAct_el {k : Nat} (hk : k ≤ 71) :
    codeAct22 (el inv22s2 k) = actM (Md.getD k []) := actC_el hk

theorem codeFixMasks_eq {l : List T22s2.Elem}
    (hl : ∀ a ∈ l, a * a = 1) : codeFixMasks22 l = fixMasks 10 codeAct22 l := by
  cases l with
  | nil => rfl
  | cons a l =>
    have ha := hl a List.mem_cons_self
    have e : codeFixTab22[a.idx]! = fixMasks 10 codeAct22 [a] := by
      rw [codeFixTab22, getElem!_pos _ a.idx (by simpa using a.lt), Array.getElem_ofFn]
      have : T22s2.elemEquiv.symm ⟨a.idx, a.lt⟩ = a := rfl
      simp only [this, ha, ↓reduceIte]
    rw [codeFixMasks22, e, ← fixMasks_cons]

theorem codeAct_mem {x : T22s2.Elem} (hx : x ∈ inv22s2) :
    codeAct22 x = actM (Md.getD (inv22s2.idxOf x) []) := by
  rw [← codeAct_el (by rw [← len]; exact idxOf_le x), el_idxOf (Or.inl hx)]

theorem act_mem {x : T22s2.Elem} (hx : x ∈ inv22s2) :
    act22s2 x = actM (Mc.getD (inv22s2.idxOf x) []) := by
  rw [← act_el (by rw [← len]; exact idxOf_le x), el_idxOf (Or.inl hx)]

theorem arr_get (p : T22s2.Elem) {i : Nat} (hi : i < 24) :
    (T22s2.arr p)[i]! = CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) (pk E p) i :=
  pg_pk packed p hi

end CertificateChecks.KernelHMathieu.T22

end
