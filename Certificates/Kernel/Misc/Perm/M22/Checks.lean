module

public import Certificates.Kernel.Misc.Perm.M22.Data
import CFSG.Certificates.Kernel.LocalQTPermSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.M22

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.LQT.P

theorem treeB : allN 20160 (treeAt (mul 22) (one 22) KG 2 E PA) = true := by decide +kernel
theorem sortB : allN 20160 (sortAt 20160 E SG) = true := by decide +kernel
theorem closedB : allN 20160 (closedAt (mul 22) KG 2 20160 E CT) = true := by decide +kernel

theorem img_mulP {n s t i : Nat} (hi : i < n) : img (mul n s t) i = img s (img t i) := by
  have hlt : ∀ j < n, img s (img t j) < 32 := fun j _ => by
    rw [CFSG.KC.LQT.P.img_eq]
    exact Nat.mod_lt _ (by omega)
  unfold mul
  rw [CFSG.KC.LQT.P.ofFn_eq, CFSG.KC.LQT.P.img_eq (CFSG.KC.LQT.P.E _ n) i]
  exact CFSG.KC.LQT.P.E_digit hlt hi

theorem beq_mul (n a b c d : Nat) : Nat.beq (mul n a b) (mul n c d) =
    allN n (fun i => Nat.beq (img a (img b i)) (img c (img d i))) := by
  cases h : allN n (fun i => Nat.beq (img a (img b i)) (img c (img d i)))
  · cases e : Nat.beq (mul n a b) (mul n c d)
    · rfl
    · have e' := Nat.eq_of_beq_eq_true e
      have ht : allN n (fun i => Nat.beq (img a (img b i)) (img c (img d i))) = true :=
        (CFSG.KC.LQT.P.allN_iff _ _).2 fun i hi => by
          show Nat.beq (img a (img b i)) (img c (img d i)) = true
          rw [← img_mulP hi, ← img_mulP hi, e']
          exact Nat.beq_refl _
      rw [h] at ht
      exact absurd ht (by decide)
  · have hp := (CFSG.KC.LQT.P.allN_iff _ _).1 h
    have e : mul n a b = mul n c d := by
      unfold mul
      rw [CFSG.KC.LQT.P.ofFn_eq, CFSG.KC.LQT.P.ofFn_eq]
      exact CFSG.KC.LQT.P.E_congr fun i hi => Nat.eq_of_beq_eq_true (hp i hi)
    rw [e]
    exact Nat.beq_refl _

@[expose] noncomputable def noBadF (X Y : Nat) (W : Nat → Nat) (Q : List Nat) (g : Nat) : Bool :=
  allN 9 fun k => impB (allN 22 fun i => Nat.beq (img g (img X i)) (img (W k) (img g i)))
    (allN 9 fun l => impB (allN 22 fun i => Nat.beq (img g (img Y i)) (img (W l) (img g i)))
      (q8K Q k l))

theorem noBadK_eqF (X Y : Nat) (W : Nat → Nat) (Q : List Nat) (g : Nat) :
    noBadK X Y W Q g = noBadF X Y W Q g := by
  unfold noBadK noBadF
  simp only [CFSG.KC.LQT.P.letB_eq, beq_mul]

@[expose] noncomputable def badF (k : Nat) : Bool :=
  noBadF xC yC WC q8L (CertificateChecks.KernelMisc.M22.E k)

theorem badFB : allN 20160 badF = true := by decide +kernel

theorem badB : allN 20160 badAt = true := by
  have e : badAt = badF :=
    funext fun k => noBadK_eqF xC yC WC q8L (CertificateChecks.KernelMisc.M22.E k)
  rw [e]
  exact badFB

theorem twB : allN 22 (wordAt 22 AG 2 TW T) = true := by decide +kernel
theorem kwB : allN 2 (wordAt 22 AG 2 KW KG) = true := by decide +kernel
theorem coverB : allN 22 (coverAt 22 AG 2 22 T 20160 E IX) = true := by decide +kernel
theorem fixB : allN 22 (fun j => impB (Nat.blt 0 j) (notB (Nat.beq (img (T j) 0) 0))) = true := by
  decide +kernel
theorem kfixB : allN 2 (fun j => Nat.beq (img (KG j) 0) 0) = true := by decide +kernel
theorem t0B : Nat.beq (T 0) (one 22) = true := by decide +kernel

end CertificateChecks.KernelMisc.M22

end
