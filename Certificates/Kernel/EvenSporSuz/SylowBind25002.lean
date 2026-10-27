module

public import Certificates.Data.Kernel.EvenSporSuz.Sylow
public import Certificates.Kernel.EvenSporSuz.SylowData25002
public import Certificates.Kernel.EvenSporSuz.Data
public import CFSG.Certificates.Kernel.Common.EachTrue
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSyl25002

open CFSG.KC.EvenSporSuz CFSG.KC.EvenSporSuz.Syl CFSG.KC.Misc.G24 CertificateChecks.KernelSuz

@[expose] noncomputable def aL : Nat := lanesL (cgL 7)

@[expose] noncomputable def bL : Nat := lanesL (cgL 8)

@[expose] noncomputable def abL : List Nat :=
  [aL, mulF3 aL aL, mulF3 (mulF3 aL aL) aL, bL, mulF3 bL bL]

@[expose] noncomputable def abiL : List Nat :=
  [mulF3 (mulF3 aL aL) aL, mulF3 aL aL, aL, mulF3 bL bL, bL]

@[expose] noncomputable def bindG (k : Nat) : Bool :=
  Nat.beq (gs.getD k 0) (evalL abL abiL ((natsK (swL (k + 1))).map (2 * ·)))

@[expose] noncomputable def bindX : Bool :=
  ((swL 7).splitOn ' ').all tokK && digitsK (swL 8) && Nat.beq (CFSG.KC.Str.decVal (swL 8)) 14 &&
    Nat.beq x1 (evalL gs gi (lettersK (swL 5))) && Nat.beq x2 (evalL gs gi (lettersK (swL 6))) &&
    Nat.beq z (evalL gs gi (lettersK (swL 7)))

@[expose] noncomputable def wordAB (L : List Char) : List Nat :=
  bif L.isEmpty then [] else (natsK L).map (2 * ·)

@[expose] noncomputable def bindR (k : Nat) : Bool :=
  ((swL (9 + 3 * k)).splitOn ' ').all tokK &&
    ((swL (10 + 3 * k)).isEmpty || ((swL (10 + 3 * k)).splitOn ' ').all digitsK) &&
    digitsK (swL (11 + 3 * k)) && Nat.beq (tg.getD k 0) (CFSG.KC.Str.decVal (swL (11 + 3 * k))) &&
    Nat.beq (r.getD k 0) (evalL gs gi (lettersK (swL (9 + 3 * k)))) &&
    Nat.beq (c.getD k 0) (evalL abL abiL (wordAB (swL (10 + 3 * k))))

set_option maxHeartbeats 0 in
theorem bindX_true : bindX = true := by decide +kernel

#kc_each CertificateChecks.KernelSyl25002 bindG25002 (fun k => bindG k) 0 4

#kc_each CertificateChecks.KernelSyl25002 bindR25002 (fun k => bindR k) 0 14

set_option maxHeartbeats 0 in
theorem bindG_bad : (!Nat.beq (gs.getD 1 0) (evalL abL abiL ((natsK (swL 1)).map (2 * ·)))) =
    true := by decide +kernel

end CertificateChecks.KernelSyl25002
