
module

public import Certificates.Kernel.HMathieu.T24
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import CFSG.Quasithin.Background.HFCodeInputs

public section

namespace CertificateChecks.KernelHMathieu.T24

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu

theorem t24_eq : T24s2 = PT.ofGens 24 (gens.map unpk) 64 := by
  unfold T24s2
  congr 1

theorem packed : Packed T24s2 E where
  elems := by
    rw [t24_eq]
    change bfsClosure 24 (gens.map unpk) 64 = _
    rw [bfsClosure_eq (List.all_eq_true.1 vpG), bfs]
  one := by rw [t24_eq]; rfl
  vp := List.all_eq_true.1 vpE

theorem invData : InvData T24s2 E inv P :=
  ⟨by rw [invols_idx packed, invOK], pOK⟩

theorem len : inv24s2.length = 191 := by
  rw [inv24s2, length_invols invData, lenOK.1]

theorem gtabs : GTabs inv24s2 (cmD rows) (mkD rows) :=
  gtabs_of packed invData (by rw [lenOK.1]; exact tabs)

theorem lenP : P.length = 192 := by rw [pOK]; simp [lenOK.1]

theorem idOK : E.getD 0 0 = pidn 24 5 := by decide +kernel

theorem act_el {k : Nat} (hk : k ≤ 191) :
    act24s2 (el inv24s2 k) = actM (Mc.getD k []) := by
  funext m
  have e := map_elems_get packed (fun a => matOf 11 (act11 a)) (el inv24s2 k)
  unfold act24s2 mats24s2 matsOf11
  have hk' : k ≤ T24s2.invols.length := by rw [← inv24s2, len]; exact hk
  rw [e, show inv24s2 = T24s2.invols from rfl, pk_el packed invData hk', mcOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [lenP]; omega) _ 0]
  unfold matP
  congr 1

theorem actC_el {k : Nat} (hk : k ≤ 191) :
    (fun m => actM (matsC24[(el inv24s2 k).idx]!) m) = actM (Md.getD k []) := by
  funext m
  have e := map_elems_get packed (fun a => matOf 11 (actC11 a)) (el inv24s2 k)
  unfold matsC24 matsOfC11
  have hk' : k ≤ T24s2.invols.length := by rw [← inv24s2, len]; exact hk
  rw [e, show inv24s2 = T24s2.invols from rfl, pk_el packed invData hk', mdOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [lenP]; omega) _ 0]
  unfold matP
  congr 1

theorem codeAct_el {k : Nat} (hk : k ≤ 191) :
    codeAct24 (el inv24s2 k) = actM (Md.getD k []) := actC_el hk

theorem codeFixMasks_eq {l : List T24s2.Elem}
    (hl : ∀ a ∈ l, a * a = 1) : codeFixMasks24 l = fixMasks 11 codeAct24 l := by
  cases l with
  | nil => rfl
  | cons a l =>
    have ha := hl a List.mem_cons_self
    have e : codeFixTab24[a.idx]! = fixMasks 11 codeAct24 [a] := by
      rw [codeFixTab24, getElem!_pos _ a.idx (by simpa using a.lt), Array.getElem_ofFn]
      have : T24s2.elemEquiv.symm ⟨a.idx, a.lt⟩ = a := rfl
      simp only [this, ha, ↓reduceIte]
    rw [codeFixMasks24, e, ← fixMasks_cons]

theorem codeAct_mem {x : T24s2.Elem} (hx : x ∈ inv24s2) :
    codeAct24 x = actM (Md.getD (inv24s2.idxOf x) []) := by
  rw [← codeAct_el (by rw [← len]; exact idxOf_le x), el_idxOf (Or.inl hx)]

theorem act_mem {x : T24s2.Elem} (hx : x ∈ inv24s2) :
    act24s2 x = actM (Mc.getD (inv24s2.idxOf x) []) := by
  rw [← act_el (by rw [← len]; exact idxOf_le x), el_idxOf (Or.inl hx)]

theorem act_pk (p : T24s2.Elem) {m : Nat} (hm : m < 2 ^ 11) :
    act24s2 p m = actP ccECols liftECols (pk E p) m := by
  unfold act24s2 mats24s2 matsOf11
  rw [map_elems_get packed (fun a => matOf 11 (act11 a)) p,
    actM_matOf (xorLin_act11 _) 11 m hm]
  exact actM_unpk _ _ _ _

theorem arr_get (p : T24s2.Elem) {i : Nat} (hi : i < 24) :
    (T24s2.arr p)[i]! = CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) (pk E p) i :=
  pg_pk packed p hi

end CertificateChecks.KernelHMathieu.T24

end
