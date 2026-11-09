module

public import Certificates.Data.Kernel.SporSch.HNXBind
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit

public section

namespace CertificateChecks.KernelSporSch.HNXBind

open CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def szChk (t : OrbitNats) : Nat → Bool :=
  OrbitNats.rec (motive := fun _ => Nat → Bool)
    (fun _ c _ n => Nat.beq c n)
    (fun ls _ _ iha ihb n => and (and (iha ls) (ihb (Nat.sub n ls))) (Nat.ble ls n)) t

theorem szChk_eq (t : OrbitNats) (n : Nat) : szChk t n = shapeOK n t := by
  induction t generalizing n with
  | leaf w c b =>
    show Nat.beq c n = (true && (c == n))
    rw [Bool.true_and]; rfl
  | branch ls a b iha ihb =>
    show and (and (szChk a ls) (szChk b (n - ls))) (Nat.ble ls n) =
      ((a.valid && b.valid && a.size == ls) && (ls + b.size == n))
    rw [iha, ihb]
    unfold shapeOK
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      exact ⟨⟨⟨h1, h3⟩, h2⟩, by omega⟩
    · rintro ⟨⟨⟨h1, h3⟩, h2⟩, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3, by omega⟩, by omega⟩

@[expose] noncomputable def hnxShapeC (P : PackedOrbitData) : Bool :=
  P.dimension == 133 && szChk P.vectors 1140000 && szChk P.alpha 1140000 &&
    szChk P.beta 1140000 && szChk P.parents 1140000 && szChk P.labels 1140000

theorem hnxShapeK_eq (P : PackedOrbitData) : hnxShapeK P = hnxShapeC P := by
  unfold hnxShapeK hnxShapeC
  simp only [szChk_eq]

theorem bindS : hnxShapeK (hnsOrbitData ()) = true := by
  rw [hnxShapeK_eq]
  decide +kernel

theorem neg_shape : (!shapeOK 2 (.branch 2 (.leaf 1 1 0) (.leaf 1 1 0))) = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNXBind

end
