module

public import Certificates.Kernel.Misc.Perm.J2C3B
public import Certificates.Kernel.Misc.Perm.J2C3C
public import Certificates.Kernel.Misc.Perm.J2Fam
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.J2En "Certificates/Kernel/Misc/Perm/data/j2enum.json.gz" 1198012 12638514722076861662
  (CaP : List Nat) (CaE : List Nat) (CaR : List Nat) (CaL : List Nat)
  (NaP : List Nat) (NaE : List Nat) (NaR : List Nat) (NaL : List Nat)
  (CvP : List Nat) (CvE : List Nat) (CvR : List Nat) (CvL : List Nat)
  (NVP : List Nat) (NVE : List Nat) (NVR : List Nat) (NVL : List Nat)
  (NEP : List Nat) (NEE : List Nat) (NER : List Nat) (NEL : List Nat)
  (S0P : List Nat) (S0E : List Nat) (S0R : List Nat) (S0L : List Nat)
  (S1P : List Nat) (S1E : List Nat) (S1R : List Nat) (S1L : List Nat)
  (S2P : List Nat) (S2E : List Nat) (S2R : List Nat) (S2L : List Nat)
  (PH : List Nat)

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelMisc.J2C3 (X Z I cm keyF chunkK)
open CertificateChecks.KernelMisc.J2Fam (GA GV H1 HV NE CC V1 V2 WG U4 P0 OU)

@[expose] noncomputable def certL (N G : ℕ) (P E R L : List ℕ) : CFSG.Monster.B.Fischer.ArrCert :=
  ⟨Array.ofFn fun i : Fin N => unpack 315 9 (lget P i.val),
    Array.ofFn fun i : Fin N => Array.ofFn fun k : Fin G => lget E (G * i.val + k.val),
    Array.ofFn fun i : Fin N => lget R i.val, Array.ofFn fun i : Fin N => lget L i.val⟩

@[expose] noncomputable def cCaL : CFSG.Monster.B.Fischer.ArrCert := certL 36 2 CaP CaE CaR CaL
@[expose] noncomputable def cNaL : CFSG.Monster.B.Fischer.ArrCert := certL 72 3 NaP NaE NaR NaL
@[expose] noncomputable def cCvL : CFSG.Monster.B.Fischer.ArrCert := certL 240 2 CvP CvE CvR CvL
@[expose] noncomputable def cNVL : CFSG.Monster.B.Fischer.ArrCert := certL 720 3 NVP NVE NVR NVL
@[expose] noncomputable def cNEL : CFSG.Monster.B.Fischer.ArrCert := certL 54 3 NEP NEE NER NEL

@[expose] noncomputable def cSL (k : ℕ) : CFSG.Monster.B.Fischer.ArrCert :=
  if k = 0 then certL 64 4 S0P S0E S0R S0L
  else if k = 1 then certL 64 4 S1P S1E S1R S1L else certL 64 4 S2P S2E S2R S2L

@[expose] noncomputable def inv (p : ℕ) : ℕ := pinvS 315 9 (mask 9) p

@[expose] noncomputable def pw (p e : ℕ) : ℕ := ppow 315 9 (mask 9) (pidn 315 9) p e

@[expose] noncomputable def cj (f p : ℕ) : ℕ := cm f (cm p (inv f))

@[expose] noncomputable def commK (p q : ℕ) : Bool := Nat.beq (cm p q) (cm q p)

@[expose] noncomputable def memL (l : List ℕ) (p : ℕ) : Bool := l.any (Nat.beq p)

@[expose] noncomputable def GCa : ℕ → ℕ := lget [GA 0, GA 1]
@[expose] noncomputable def GNa : ℕ → ℕ := lget [GA 0, GA 1, H1]
@[expose] noncomputable def GCv : ℕ → ℕ := lget [GV 0, GV 1]
@[expose] noncomputable def GNV : ℕ → ℕ := lget [GV 0, GV 1, HV]
@[expose] noncomputable def GNE : ℕ → ℕ := lget [X, NE 0, NE 1]

@[expose] noncomputable def VK (k i : ℕ) : ℕ := cj (CC k) (cond (Nat.beq i 1) V1 V2)

@[expose] noncomputable def GS0 : ℕ → ℕ := lget [VK 0 1, VK 0 2, VK 1 1, VK 1 2]
@[expose] noncomputable def GS1 : ℕ → ℕ := lget [VK 0 1, VK 0 2, VK 2 1, VK 2 2]
@[expose] noncomputable def GS2 : ℕ → ℕ := lget [VK 1 1, VK 1 2, VK 2 1, VK 2 2]

@[expose] noncomputable def EL (G : ℕ) (E : List ℕ) (i k : ℕ) : ℕ :=
  lget E (Nat.add (Nat.mul G i) k)

@[expose] noncomputable def ptCa : ℕ → Bool :=
  chunkK 36 (pointK 315 9 2 36 GCa (lget CaP) (EL 2 CaE) (lget CaR) (lget CaL))
@[expose] noncomputable def kyCa : ℕ → Bool := chunkK 36 (keyF (lget CaP))
@[expose] noncomputable def ptNa : ℕ → Bool :=
  chunkK 72 (pointK 315 9 3 72 GNa (lget NaP) (EL 3 NaE) (lget NaR) (lget NaL))
@[expose] noncomputable def kyNa : ℕ → Bool := chunkK 72 (keyF (lget NaP))
@[expose] noncomputable def ptCv : ℕ → Bool :=
  chunkK 60 (pointK 315 9 2 240 GCv (lget CvP) (EL 2 CvE) (lget CvR) (lget CvL))
@[expose] noncomputable def kyCv : ℕ → Bool := chunkK 60 (keyF (lget CvP))
@[expose] noncomputable def ptNV : ℕ → Bool :=
  chunkK 90 (pointK 315 9 3 720 GNV (lget NVP) (EL 3 NVE) (lget NVR) (lget NVL))
@[expose] noncomputable def kyNV : ℕ → Bool := chunkK 90 (keyF (lget NVP))
@[expose] noncomputable def ptNE : ℕ → Bool :=
  chunkK 54 (pointK 315 9 3 54 GNE (lget NEP) (EL 3 NEE) (lget NER) (lget NEL))
@[expose] noncomputable def kyNE : ℕ → Bool := chunkK 54 (keyF (lget NEP))
@[expose] noncomputable def ptS0 : ℕ → Bool :=
  chunkK 64 (pointK 315 9 4 64 GS0 (lget S0P) (EL 4 S0E) (lget S0R) (lget S0L))
@[expose] noncomputable def kyS0 : ℕ → Bool := chunkK 64 (keyF (lget S0P))
@[expose] noncomputable def ptS1 : ℕ → Bool :=
  chunkK 64 (pointK 315 9 4 64 GS1 (lget S1P) (EL 4 S1E) (lget S1R) (lget S1L))
@[expose] noncomputable def kyS1 : ℕ → Bool := chunkK 64 (keyF (lget S1P))
@[expose] noncomputable def ptS2 : ℕ → Bool :=
  chunkK 64 (pointK 315 9 4 64 GS2 (lget S2P) (EL 4 S2E) (lget S2R) (lget S2L))
@[expose] noncomputable def kyS2 : ℕ → Bool := chunkK 64 (keyF (lget S2P))

@[expose] noncomputable def AEK : List ℕ :=
  (List.range 3).flatMap fun a => (List.range 3).map fun c => cm (pw Z a) (pw X c)

@[expose] noncomputable def WEK (i : ℕ) : List ℕ :=
  [I, WG (2 * i + 0), WG (2 * i + 1), cm (WG (2 * i + 0)) (WG (2 * i + 1))]

@[expose] noncomputable def involK (p : ℕ) : Bool := Nat.beq (cm p p) I && !(Nat.beq p I)

@[expose] noncomputable def wK (W : ℕ → List ℕ) (p : ℕ) : Bool :=
  (!(involK p && AEK.all fun f => commK p (cj f p)) || memL (W 0) p || memL (W 1) p ||
      memL (W 2) p) &&
    [0, 1, 2].all fun i => !(commK p (WG (2 * i + 0)) && commK p (WG (2 * i + 1))) ||
      (W i).any fun w => (List.range 3).any fun e => Nat.beq p (cm w (pw Z e))

@[expose] noncomputable def e0cK (p : ℕ) : Bool := !(commK p X) || memL AEK p

@[expose] noncomputable def e0nK (M : ℕ → Bool) (p : ℕ) : Bool :=
  !(memL AEK (cj p Z) && memL AEK (cj p X)) || M p

@[expose] noncomputable def two8K (p : ℕ) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q) (fun _ ih q => ih (cm q q)) 8 p) I

@[expose] noncomputable def outK (u p : ℕ) : Bool :=
  !(two8K (cm p u) && [GA 0, GA 1, H1].all fun n => two8K (cm (cm p u) (cj n (cm p u))))

@[expose] noncomputable def sczK (p : ℕ) : Bool := !(commK p Z) || memL (WEK 0) p

@[expose] noncomputable def VEK : List ℕ := [I, V1, V2, cm V1 V2]

@[expose] noncomputable def SPK : List ℕ :=
  (WEK 0).flatMap fun w => (List.range 4).flatMap fun e => (List.range 4).map fun f =>
    cm w (cm (cj (CC 0) (lget VEK e)) (cj (CC 1) (lget VEK f)))

@[expose] noncomputable def sprodK (p : ℕ) : Bool := memL SPK p

@[expose] noncomputable def phiK (a b c : ℕ) : ℕ :=
  cm (cm (pw (U4 0) (a % 2)) (pw (U4 1) (a / 2)))
    (cm (cm (pw (U4 2) (b % 2)) (pw (U4 3) (b / 2)))
      (cm (pw (cm (cm (U4 0) (U4 2)) (cm (inv (U4 0)) (inv (U4 2)))) (c % 2))
        (pw (cm (cm (U4 0) (U4 3)) (cm (inv (U4 0)) (inv (U4 3)))) (c / 2))))

@[expose] noncomputable def phT (a b c : ℕ) : ℕ := lget PH (16 * a + 4 * b + c)

@[expose] noncomputable def phK (j : ℕ) : Bool :=
  Nat.beq (lget PH j) (phiK (j / 16) (j / 4 % 4) (j % 4))

@[expose] noncomputable def lawK (a : ℕ) : Bool :=
  (List.range 4).all fun b => (List.range 4).all fun c =>
    (List.range 4).all fun a' => (List.range 4).all fun b' => (List.range 4).all fun c' =>
      Nat.beq (cm (phT a b c) (phT a' b' c'))
        (phT (a ^^^ a') (b ^^^ b')
          (c ^^^ c' ^^^ CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.mulCode4 a' b))

@[expose] noncomputable def phD (j : ℕ) : Bool :=
  CFSG.KC.LQT.P.allN j fun i => !(Nat.beq (lget PH j) (lget PH i))

@[expose] noncomputable def wCz : ℕ → Bool :=
  chunkK 90 fun k => wK WEK (CertificateChecks.KernelMisc.J2C3.CzP.F k)

@[expose] noncomputable def e0cCz : ℕ → Bool :=
  chunkK 90 fun k => e0cK (CertificateChecks.KernelMisc.J2C3.CzP.F k)

@[expose] noncomputable def e0nNZ : ℕ → Bool :=
  chunkK 90 fun k => e0nK (memK 54 (lget NEP)) (CertificateChecks.KernelMisc.J2C3.NZP.F k)

@[expose] noncomputable def outNa : ℕ → Bool := chunkK 72 fun k => outK (cm P0 OU) (lget NaP k)

@[expose] noncomputable def sczS : ℕ → Bool := chunkK 64 fun k => sczK (lget S0P k)

@[expose] noncomputable def sprodS : ℕ → Bool := chunkK 64 fun k => sprodK (lget S0P k)

@[expose] noncomputable def lawC : ℕ → Bool := chunkK 1 lawK

@[expose] noncomputable def phC : ℕ → Bool := chunkK 64 phK

@[expose] noncomputable def phDC : ℕ → Bool := chunkK 64 phD

end CertificateChecks.KernelMisc.J2En

end
