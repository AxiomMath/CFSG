module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EVS

public section

namespace CertificateChecks.KernelSpor.SuzC1EL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
  CertificateChecks.KernelSpor.SuzC1EG CertificateChecks.KernelSpor.SuzC1EF
  CertificateChecks.KernelSpor.SuzC1EV

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11
local notation "W0" => SuzTwG 6
local notation "R1" => SuzC1BT 11
local notation "Rho" => SuzTwG 2
local notation "pgk" => pg 11 (mask 11)

@[expose] noncomputable def c0K (i : Nat) : Nat := SuzC1EV.T (SuzC1EC.getD i 0)

@[expose] noncomputable def c0IK (i : Nat) : Nat := SuzC1EI (SuzC1EC.getD i 0 + 1)

@[expose] noncomputable def invOK (k : Nat) : Bool :=
  ie (SuzC1EV.T k) (SuzC1EI (k + 1)) && cn (SuzC1EI (k + 1))

@[expose] noncomputable def c0InvK (i : Nat) : Bool :=
  invOK (SuzC1EC.getD i 0) && Nat.beq (pc (c0IK i) (c0K i)) Id

@[expose] noncomputable def locK (k : Nat) : Bool :=
  strictB (SuzC1EV.T k) fun X => strictB (wg SuzC1EWL k) fun w =>
    bIf(Nat.beq w 0,
      strictB (SuzC1EI (k + 1)) fun XI => strictB (wg SuzC1EWM k) fun v =>
        strictB (Nat.mod v 16) fun i => strictB (Nat.div v 16) fun q =>
          invOK k && Nat.beq (pc XI X) Id && Nat.blt i 16 && Nat.blt q 64 &&
            (strictB (pc (pc (pc X (c0K i)) XI) (c0IK i)) fun Y =>
              !(Nat.beq (pc Y R1) (pc R1 Y) && Nat.beq (pc Y Rho) (pc Rho Y))) &&
            (strictB (SuzC1ET.T q) fun E => Nat.beq (pc E E) Id &&
              strictB (pc (pc X E) XI) fun Y => !Nat.beq (pc E Y) (pc Y E)),
      strictB (Nat.sub w 1) fun m => Nat.blt m 1024 &&
        Nat.beq (pc (SuzC1ET.T (Nat.div m 16)) (c0K (Nat.mod m 16))) X)

@[expose] noncomputable def preK (K V U Y : Nat) : Bool :=
  allBelow 4 fun i => pgk K (pgk V (pgk U i)) == pgk Y (pgk K (pgk V i))

@[expose] noncomputable def conjEqK (K V C U Y : Nat) : Bool :=
  preK K V U Y && Nat.beq (pc C U) (pc Y C)

@[expose] noncomputable def rhoTailK (C : Nat) : Bool :=
  strictB (pc C C) fun C2 => Nat.beq (pc C2 W0) (pc W0 C2) ||
    strictB (pc C C2) fun C3 => Nat.beq (pc C3 W0) (pc W0 C3) && (!Nat.beq C3 Id || cK C)

@[expose] noncomputable def rhoCandK (K V U L : Nat) : Bool :=
  bIf(preK K V U W0 || preK K V U U || preK K V U L,
    strictB (pc K V) fun C =>
      !(conjEqK K V C U W0 || conjEqK K V C U U || conjEqK K V C U L) || rhoTailK C,
    true)

@[expose] noncomputable def rhoMK (i s lo len : Nat) : Bool :=
  strictB (c0K i) fun U => strictB (pc W0 U) fun L =>
    strictB (kK (wg SuzC1EWR (2 * i + s))) fun K =>
      allBlk lo (fun m => rhoCandK K (SuzC1EV.T m) U L) len

@[expose] noncomputable def rcK (U : Nat) : Bool :=
  Nat.beq (pc U U) Id && !Nat.beq U Id && !Nat.beq U W0 && !memT U && !memT (pc W0 U)

@[expose] noncomputable def rhoHK (i s : Nat) : Bool :=
  strictB (c0K i) fun U => strictB (pc W0 U) fun L =>
    strictB (wg SuzC1EWR (2 * i + s)) fun j => strictB (kK j) fun K =>
      Nat.blt j 8 && Nat.beq (pc K W0) (pc (nIf(Nat.beq s 0, U, L)) K)

@[expose] noncomputable def rhoI (i : Nat) : Bool := !rcK (c0K i) || (rhoHK i 0 && rhoHK i 1)

@[expose] def rhoIs : List Nat := [2, 3, 8, 10, 11, 13, 14, 15]

@[expose] noncomputable def locS (t : Nat) : Bool := allBlk (64 * t) locK 64

@[expose] noncomputable def rh2a (q : Nat) : Bool := rhoMK 2 0 (16 * q) 16
@[expose] noncomputable def rh2b (q : Nat) : Bool := rhoMK 2 1 (16 * q) 16
@[expose] noncomputable def rh3a (q : Nat) : Bool := rhoMK 3 0 (16 * q) 16
@[expose] noncomputable def rh3b (q : Nat) : Bool := rhoMK 3 1 (16 * q) 16
@[expose] noncomputable def rh10b (q : Nat) : Bool := rhoMK 10 1 (16 * q) 16
@[expose] noncomputable def rh11a (q : Nat) : Bool := rhoMK 11 0 (16 * q) 16
@[expose] noncomputable def rh13a (q : Nat) : Bool := rhoMK 13 0 (16 * q) 16
@[expose] noncomputable def rh14b (q : Nat) : Bool := rhoMK 14 1 (16 * q) 16

@[expose] noncomputable def rhoLight : Bool :=
  rhoMK 8 0 0 512 && rhoMK 8 1 0 512 && rhoMK 10 0 0 512 && rhoMK 11 1 0 512 &&
    rhoMK 13 1 0 512 && rhoMK 14 0 0 512 && rhoMK 15 0 0 512 && rhoMK 15 1 0 512

end CertificateChecks.KernelSpor.SuzC1EL

end
