module

public import Certificates.Kernel.Misc.Perm.A6RepDefs

public section

namespace CertificateChecks.KernelMisc.A6Rep

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
open Equiv FieldFour

theorem supp_eq : ∀ σ : Perm (Fin 6), σ.support.card = mvd (Vector.ofFn σ) := by
  decide +kernel

theorem mem3 : ∀ σ : Perm (Fin 6), mvd (Vector.ofFn σ) = 3 → Vector.ofFn σ ∈ l3 := by
  decide +kernel

theorem memA0 : ∀ g : alternatingGroup (Fin 6), (g : Perm (Fin 6)) 0 = 0 →
    Vector.ofFn ⇑(g : Perm (Fin 6)) ∈ la0 := by
  decide +kernel

theorem memA1 : ∀ g : alternatingGroup (Fin 6), (g : Perm (Fin 6)) 0 = 1 →
    Vector.ofFn ⇑(g : Perm (Fin 6)) ∈ la1 := by
  decide +kernel

theorem memA2 : ∀ g : alternatingGroup (Fin 6), (g : Perm (Fin 6)) 0 = 2 →
    Vector.ofFn ⇑(g : Perm (Fin 6)) ∈ la2 := by
  decide +kernel

theorem memA3 : ∀ g : alternatingGroup (Fin 6), (g : Perm (Fin 6)) 0 = 3 →
    Vector.ofFn ⇑(g : Perm (Fin 6)) ∈ la3 := by
  decide +kernel

theorem memA4 : ∀ g : alternatingGroup (Fin 6), (g : Perm (Fin 6)) 0 = 4 →
    Vector.ofFn ⇑(g : Perm (Fin 6)) ∈ la4 := by
  decide +kernel

theorem memA5 : ∀ g : alternatingGroup (Fin 6), (g : Perm (Fin 6)) 0 = 5 →
    Vector.ofFn ⇑(g : Perm (Fin 6)) ∈ la5 := by
  decide +kernel

theorem memA (g : alternatingGroup (Fin 6)) : Vector.ofFn ⇑(g : Perm (Fin 6)) ∈ la := by
  unfold la
  rw [List.mem_flatten]
  generalize hk : (g : Perm (Fin 6)) 0 = k
  fin_cases k
  · exact ⟨_, by simp only [List.mem_cons, true_or, or_true], memA0 g hk⟩
  · exact ⟨_, by simp only [List.mem_cons, true_or, or_true], memA1 g hk⟩
  · exact ⟨_, by simp only [List.mem_cons, true_or, or_true], memA2 g hk⟩
  · exact ⟨_, by simp only [List.mem_cons, true_or, or_true], memA3 g hk⟩
  · exact ⟨_, by simp only [List.mem_cons, true_or, or_true], memA4 g hk⟩
  · exact ⟨_, by simp only [List.mem_cons, true_or, or_true], memA5 g hk⟩

theorem inv3_0 : e0.all invV = true := by decide +kernel

theorem inv3_1 : e1.all invV = true := by decide +kernel

theorem inv3_2 : e2.all invV = true := by decide +kernel

theorem inv3_3 : e3.all invV = true := by decide +kernel

theorem inv3_4 : e4.all invV = true := by decide +kernel

theorem inv3_5 : e5.all invV = true := by decide +kernel

theorem inv3_6 : e6.all invV = true := by decide +kernel

theorem inv3_7 : e7.all invV = true := by decide +kernel

theorem inv3_8 : e8.all invV = true := by decide +kernel

theorem inv3_9 : e9.all invV = true := by decide +kernel

theorem inv3_10 : e10.all invV = true := by decide +kernel

theorem inv3_11 : e11.all invV = true := by decide +kernel

theorem inv3_12 : e12.all invV = true := by decide +kernel

theorem inv3_13 : e13.all invV = true := by decide +kernel

theorem inv3_14 : e14.all invV = true := by decide +kernel

theorem inv3_15 : e15.all invV = true := by decide +kernel

theorem inv3_16 : e16.all invV = true := by decide +kernel

theorem inv3_17 : e17.all invV = true := by decide +kernel

theorem inv3_18 : e18.all invV = true := by decide +kernel

theorem inv3_19 : e19.all invV = true := by decide +kernel

theorem inv3 : ∀ v ∈ l3, invV v = true :=
  allFlatB <| List.forall_mem_cons.2 ⟨inv3_0, List.forall_mem_cons.2 ⟨inv3_1,
    List.forall_mem_cons.2 ⟨inv3_2, List.forall_mem_cons.2 ⟨inv3_3,
    List.forall_mem_cons.2 ⟨inv3_4, List.forall_mem_cons.2 ⟨inv3_5,
    List.forall_mem_cons.2 ⟨inv3_6, List.forall_mem_cons.2 ⟨inv3_7,
    List.forall_mem_cons.2 ⟨inv3_8, List.forall_mem_cons.2 ⟨inv3_9,
    List.forall_mem_cons.2 ⟨inv3_10, List.forall_mem_cons.2 ⟨inv3_11,
    List.forall_mem_cons.2 ⟨inv3_12, List.forall_mem_cons.2 ⟨inv3_13,
    List.forall_mem_cons.2 ⟨inv3_14, List.forall_mem_cons.2 ⟨inv3_15,
    List.forall_mem_cons.2 ⟨inv3_16, List.forall_mem_cons.2 ⟨inv3_17,
    List.forall_mem_cons.2 ⟨inv3_18, List.forall_mem_cons.2 ⟨inv3_19,
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem invAll : ∀ σ : Perm (Fin 6), invCheckIfThreeCycle σ = true := by
  intro σ
  unfold invCheckIfThreeCycle
  rw [supp_eq σ]
  split_ifs with h
  · exact inv3 _ (mem3 σ h)
  · rfl

end CertificateChecks.KernelMisc.A6Rep

end
