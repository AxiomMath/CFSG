module

public import Certificates.Kernel.Misc.Perm.A6RepInv
public import Certificates.Kernel.Misc.Perm.A6RepNorton
public import Certificates.Kernel.Misc.Perm.A6RepCls0
public import Certificates.Kernel.Misc.Perm.A6RepCls1
public import Certificates.Kernel.Misc.Perm.A6RepSum0
public import Certificates.Kernel.Misc.Perm.A6RepSum1

public section

namespace CertificateChecks.KernelMisc.A6Rep

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
open Equiv FieldFour

theorem clsA0 : ∀ v ∈ la0, classCheckElem v = true :=
  allFlatB <| List.forall_mem_cons.2 ⟨cls0, List.forall_mem_cons.2 ⟨cls1, List.forall_mem_cons.2
    ⟨cls2, List.forall_mem_cons.2 ⟨cls3, List.forall_mem_cons.2 ⟨cls4,
    List.forall_mem_cons.2 ⟨cls5, List.forall_mem_cons.2 ⟨cls6, List.forall_mem_cons.2
    ⟨cls7, List.forall_mem_cons.2 ⟨cls8, List.forall_mem_cons.2 ⟨cls9,
    List.forall_mem_cons.2 ⟨cls10, List.forall_mem_cons.2 ⟨cls11, List.forall_mem_nil
    _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem clsA1 : ∀ v ∈ la1, classCheckElem v = true :=
  allFlatB <| List.forall_mem_cons.2 ⟨cls12, List.forall_mem_cons.2 ⟨cls13,
    List.forall_mem_cons.2 ⟨cls14, List.forall_mem_cons.2 ⟨cls15,
    List.forall_mem_cons.2 ⟨cls16, List.forall_mem_cons.2 ⟨cls17,
    List.forall_mem_cons.2 ⟨cls18, List.forall_mem_cons.2 ⟨cls19,
    List.forall_mem_cons.2 ⟨cls20, List.forall_mem_cons.2 ⟨cls21,
    List.forall_mem_cons.2 ⟨cls22, List.forall_mem_cons.2 ⟨cls23, List.forall_mem_nil
    _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem clsA2 : ∀ v ∈ la2, classCheckElem v = true :=
  allFlatB <| List.forall_mem_cons.2 ⟨cls24, List.forall_mem_cons.2 ⟨cls25,
    List.forall_mem_cons.2 ⟨cls26, List.forall_mem_cons.2 ⟨cls27,
    List.forall_mem_cons.2 ⟨cls28, List.forall_mem_cons.2 ⟨cls29,
    List.forall_mem_cons.2 ⟨cls30, List.forall_mem_cons.2 ⟨cls31,
    List.forall_mem_cons.2 ⟨cls32, List.forall_mem_cons.2 ⟨cls33,
    List.forall_mem_cons.2 ⟨cls34, List.forall_mem_cons.2 ⟨cls35, List.forall_mem_nil
    _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem clsA3 : ∀ v ∈ la3, classCheckElem v = true :=
  allFlatB <| List.forall_mem_cons.2 ⟨cls36, List.forall_mem_cons.2 ⟨cls37,
    List.forall_mem_cons.2 ⟨cls38, List.forall_mem_cons.2 ⟨cls39,
    List.forall_mem_cons.2 ⟨cls40, List.forall_mem_cons.2 ⟨cls41,
    List.forall_mem_cons.2 ⟨cls42, List.forall_mem_cons.2 ⟨cls43,
    List.forall_mem_cons.2 ⟨cls44, List.forall_mem_cons.2 ⟨cls45,
    List.forall_mem_cons.2 ⟨cls46, List.forall_mem_cons.2 ⟨cls47, List.forall_mem_nil
    _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem clsA4 : ∀ v ∈ la4, classCheckElem v = true :=
  allFlatB <| List.forall_mem_cons.2 ⟨cls48, List.forall_mem_cons.2 ⟨cls49,
    List.forall_mem_cons.2 ⟨cls50, List.forall_mem_cons.2 ⟨cls51,
    List.forall_mem_cons.2 ⟨cls52, List.forall_mem_cons.2 ⟨cls53,
    List.forall_mem_cons.2 ⟨cls54, List.forall_mem_cons.2 ⟨cls55,
    List.forall_mem_cons.2 ⟨cls56, List.forall_mem_cons.2 ⟨cls57,
    List.forall_mem_cons.2 ⟨cls58, List.forall_mem_cons.2 ⟨cls59, List.forall_mem_nil
    _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem clsA5 : ∀ v ∈ la5, classCheckElem v = true :=
  allFlatB <| List.forall_mem_cons.2 ⟨cls60, List.forall_mem_cons.2 ⟨cls61,
    List.forall_mem_cons.2 ⟨cls62, List.forall_mem_cons.2 ⟨cls63,
    List.forall_mem_cons.2 ⟨cls64, List.forall_mem_cons.2 ⟨cls65,
    List.forall_mem_cons.2 ⟨cls66, List.forall_mem_cons.2 ⟨cls67,
    List.forall_mem_cons.2 ⟨cls68, List.forall_mem_cons.2 ⟨cls69,
    List.forall_mem_cons.2 ⟨cls70, List.forall_mem_cons.2 ⟨cls71, List.forall_mem_nil
    _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem clsA : ∀ v ∈ la, classCheckElem v = true :=
  allFlat <| List.forall_mem_cons.2 ⟨clsA0, List.forall_mem_cons.2 ⟨clsA1,
    List.forall_mem_cons.2 ⟨clsA2, List.forall_mem_cons.2 ⟨clsA3,
    List.forall_mem_cons.2 ⟨clsA4, List.forall_mem_cons.2 ⟨clsA5, List.forall_mem_nil
    _⟩⟩⟩⟩⟩⟩

theorem classCheckWith_true (all : Multiset (Vector (Fin 6) 6))
    (h : ∀ v ∈ all, classCheckElem v = true) : classCheckWith all = true := by
  unfold classCheckWith
  exact decide_eq_true h

theorem allImages_spec : ∀ v ∈ allImages, classCheckElem v = true := by
  intro v hv
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.1 hv
  exact clsA _ (memA g)

theorem classAll : classCheck = true :=
  classCheckWith_true allImages allImages_spec


theorem sel_eq (g : alternatingGroup (Fin 6)) :
    selectFiveCycle g = selV (Vector.ofFn ⇑(g : Perm (Fin 6))) := by
  unfold selectFiveCycle selV
  rw [supp_eq]
  rfl

theorem fold_eq (s : Multiset (alternatingGroup (Fin 6))) :
    s.foldr fiveCycleStep zeroTab16 =
      (s.map fun g : alternatingGroup (Fin 6) => Vector.ofFn ⇑(g : Perm (Fin 6))).foldr stepV
        zeroTab16 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons g s ih => rw [Multiset.foldr_cons, Multiset.map_cons, Multiset.foldr_cons, ih,
      fiveCycleStep, stepV, sel_eq]

theorem ofFn_inj : Function.Injective fun g : alternatingGroup (Fin 6) =>
    Vector.ofFn ⇑(g : Perm (Fin 6)) := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hx := congrArg (fun v : Vector (Fin 6) 6 => v[x]) hgh
  simpa using hx

theorem card_A6 : (Finset.univ : Finset (alternatingGroup (Fin 6))).card = 360 := by
  decide +kernel

theorem map_eq : ((Finset.univ : Finset (alternatingGroup (Fin 6))).val.map
    fun g : alternatingGroup (Fin 6) => Vector.ofFn ⇑(g : Perm (Fin 6))) =
      ↑la := by
  have hnd := Multiset.Nodup.map ofFn_inj (Finset.univ : Finset (alternatingGroup (Fin 6))).nodup
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun v hv => ?_) ?_
  · obtain ⟨g, -, rfl⟩ := Multiset.mem_map.1 hv
    exact Multiset.mem_coe.2 (memA g)
  · have hl : la.length = 360 := by decide +kernel
    rw [Multiset.card_map, Multiset.coe_card, Finset.card_val, card_A6, hl]

theorem omega_t0 : isOmegaScalar (rep8aOfKron t0) = true := by decide +kernel

theorem sum_eq : sumFiveCycles (Finset.univ : Finset (alternatingGroup (Fin 6))).val = t0 := by
  unfold sumFiveCycles
  rw [fold_eq, map_eq, Multiset.coe_foldr]
  simp only [la, la0, la1, la2, la3, la4, la5, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.foldr_append]
  rw [sum71, sum70, sum69, sum68, sum67, sum66, sum65, sum64, sum63, sum62, sum61,
    sum60, sum59, sum58, sum57, sum56, sum55, sum54, sum53, sum52, sum51, sum50,
    sum49, sum48, sum47, sum46, sum45, sum44, sum43, sum42, sum41, sum40, sum39,
    sum38, sum37, sum36, sum35, sum34, sum33, sum32, sum31, sum30, sum29, sum28,
    sum27, sum26, sum25, sum24, sum23, sum22, sum21, sum20, sum19, sum18, sum17,
    sum16, sum15, sum14, sum13, sum12, sum11, sum10, sum9, sum8, sum7, sum6, sum5,
    sum4, sum3, sum2, sum1, sum0]

theorem sumAll : classSumCheck = true :=
  (congrArg (fun T => isOmegaScalar (rep8aOfKron T)) sum_eq).trans omega_t0

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix in
open Matrix Equiv FieldFour in
open scoped Kronecker in
theorem facts : (
    ∀ σ : Perm (Fin 6), invCheckIfThreeCycle σ = true
  ) ∧ (
    cert8a.check rep8aTab = true
  ) ∧ (
    classCheck = true
  ) ∧ (
    classSumCheck = true
  ) := ⟨invAll, cert8aOK, classAll, sumAll⟩

end CertificateChecks.KernelMisc.A6Rep

end
