module

public import Certificates.Kernel.P1L43.Cls
public import Certificates.Kernel.P1L43.Grp
public import Certificates.Kernel.P1L43.CentA
public import Certificates.Kernel.P1L43.CentB
public import Certificates.Kernel.SchreierFam.L43Chain
public import Certificates.Data.Kernel.OrbFind

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelP1L43

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.OrbFind
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

@[expose] noncomputable def pc (P Q : Nat) : Nat := pcomp 80 7 (mask 7) P Q

@[expose] noncomputable def pk (a : Array Nat) : Nat := (packL 7 a.toList).1

@[expose] noncomputable def sP (P : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight P (nat_lit 560)) (nat_lit 0),
    bAnd(allN 80 (fun i => Nat.blt (pg 7 (mask 7) P i) 80),
      siftK 80 7 (mask 7) (80 * 7) (pidn 80 7) CertificateChecks.KernelSchreierFam.L43.LR
        CertificateChecks.KernelSchreierFam.L43.TRI CertificateChecks.KernelSchreierFam.L43.BP 6 0 P))

@[expose] noncomputable def cm (P Q : Nat) : Bool := eq22 80 7 (mask 7) P Q Q P

@[expose] noncomputable def bindT (T : Table) (P : Nat) : Bool := arrBind (natArr T) 80 7 P

@[expose] noncomputable def selfInv (P : Nat) : Bool :=
  CFSG.KC.Enum.permOK 80 7 (mask 7) (80 * 7) P P

@[expose] noncomputable def m2106 (v : Nat) : Bool := memK 80 7 ps K2106.N K2106.T K2106.S v
@[expose] noncomputable def m5265 (v : Nat) : Bool := memK 80 7 ps K5265.N K5265.T K5265.S v
@[expose] noncomputable def m1080 (v : Nat) : Bool := memK 80 7 ps K1080.N K1080.T K1080.S v
@[expose] noncomputable def m10530 (v : Nat) : Bool := memK 80 7 ps K10530.N K10530.T K10530.S v
@[expose] noncomputable def m117a (v : Nat) : Bool := memK 80 7 ps K117a.N K117a.T K117a.S v
@[expose] noncomputable def m117b (v : Nat) : Bool := memK 80 7 ps K117b.N K117b.T K117b.S v
@[expose] noncomputable def m8424 (v : Nat) : Bool := memK 80 7 ps K8424.N K8424.T K8424.S v

@[expose] noncomputable def memD (v : Nat) : Bool := m2106 v || m5265 v || m1080 v

@[expose] noncomputable def memS (v : Nat) : Bool :=
  m2106 v || m5265 v || m10530 v || m117a v || m117b v

@[expose] noncomputable def memDS (v : Nat) : Bool := m2106 v || m5265 v || m8424 v

@[expose] noncomputable def good (v : Nat) : Bool := m2106 v || m8424 v

@[expose] noncomputable def UD : Nat := pk (natArr uD)
@[expose] noncomputable def US : Nat := pk (natArr uS)
@[expose] noncomputable def UDS : Nat := pk (natArr uDS)

theorem binds :
    bindT uD UD = true ∧ bindT uS US = true ∧ bindT uDS UDS = true ∧
    bindT (tm codeA) (K2106.G 0) = true ∧ bindT (tm codeB) (K2106.G 1) = true ∧
    (List.all [K5265.G 0, K1080.G 0, K10530.G 0, K117a.G 0, K117b.G 0, K8424.G 0]
      (Nat.beq · (K2106.G 0))) = true ∧
    (List.all [K5265.G 1, K1080.G 1, K10530.G 1, K117a.G 1, K117b.G 1, K8424.G 1]
      (Nat.beq · (K2106.G 1))) = true ∧
    bindT (tm 11821474) (K2106.T K2106.r0) = true ∧ bindT (tm 40942156) (K2106.T K2106.r1) = true ∧
    bindT (tm 12703935) (K2106.T K2106.r2) = true ∧ bindT (tm 38855539) (K5265.T K5265.r0) = true ∧
    bindT (tm 28874841) (K5265.T K5265.r1) = true ∧ bindT (tm 28777033) (K5265.T K5265.r2) = true ∧
    bindT (tm 14650228) (K1080.T K1080.r0) = true ∧ bindT (ts 6629227) (K10530.T K10530.r0) = true ∧
    bindT (ts 12439050) (K117a.T K117a.r0) = true ∧ bindT (ts 12940497) (K117b.T K117b.r0) = true ∧
    bindT (ts 7174611) (K8424.T K8424.r0) = true ∧
    bindT (tm 10394616) (CD0.G 0) = true ∧ bindT (tm 17819842) (CD0.G 1) = true ∧
    bindT (tm 15481057) (CD1.G 0) = true ∧ bindT (tm 42492655) (CD1.G 1) = true ∧
    bindT (tm 34288414) (CD2.G 0) = true ∧ bindT (tm 37099471) (CD2.G 1) = true ∧
    bindT (tm 6388611) (CS0.G 0) = true ∧ bindT (tm 11307727) (CS0.G 1) = true ∧
    bindT (tm 16162266) (CS1.G 0) = true ∧ bindT (tm 37212132) (CS1.G 1) = true ∧
    bindT (tm 23277730) (CS2.G 0) = true ∧ bindT (tm 40696764) (CS2.G 1) = true ∧
    bindT (tm 39850015) (CS3.G 0) = true ∧ bindT (tm 22163176) (CS3.G 1) = true ∧
    bindT (tm 15086220) (CS4.G 0) = true ∧ bindT (tm 39271333) (CS4.G 1) = true ∧
    bindT (tm 8629557) (CDS0.G 0) = true ∧ bindT (tm 8883729) (CDS0.G 1) = true ∧
    bindT (tm 19240684) (CDS1.G 0) = true ∧ bindT (tm 32466360) (CDS1.G 1) = true ∧
    bindT (tm 1288381) (CDS2.G 0) = true ∧ bindT (tm 660594) (CDS2.G 1) = true ∧
    [UD, US, UDS, K2106.T K2106.r0, K2106.T K2106.r1, K2106.T K2106.r2, K5265.T K5265.r0,
      K5265.T K5265.r1, K5265.T K5265.r2, K1080.T K1080.r0, K10530.T K10530.r0, K117a.T K117a.r0,
      K117b.T K117b.r0, K8424.T K8424.r0].all selfInv = true := by
  decide +kernel

@[expose] noncomputable def runK (U : Nat) (G : Nat → Nat) (ng : Nat) : Bool :=
  bAnd(isIdK 80 7 (pc U U), bAnd(sP (pc U (pc (K2106.G 0) U)),
    bAnd(sP (pc U (pc (K2106.G 1) U)), allN ng fun k => sP (G k) || sP (pc (G k) U))))

theorem runs : runK UD SD.G SD.ng = true ∧ runK US SS.G SS.ng = true ∧
    runK UDS SDS.G SDS.ng = true := by
  decide +kernel

@[expose] noncomputable def coverK (mem : Nat → Bool) (N : Nat) (T : Nat → Nat) : Bool :=
  allN N fun i => strictB (T i) fun v => !isInvK 80 7 v || mem v

theorem coverD : coverK memD SD.N SD.T = true := by decide +kernel
theorem coverS : coverK memS SS.N SS.T = true := by decide +kernel
theorem coverDS : coverK memDS SDS.N SDS.T = true := by decide +kernel

@[expose] noncomputable def uclK (mem : Nat → Bool) (U : Nat) (ts : List Nat) : Bool :=
  ts.all fun t => mem (pc U (pc t U))

theorem ucl :
    uclK memD UD [K2106.T K2106.r0, K1080.T K1080.r0, K5265.T K5265.r0] = true ∧
    uclK memS US [K2106.T K2106.r1, K10530.T K10530.r0, K5265.T K5265.r1, K117a.T K117a.r0,
      K117b.T K117b.r0] = true ∧
    uclK memDS UDS [K5265.T K5265.r2, K2106.T K2106.r2, K8424.T K8424.r0] = true := by
  decide +kernel

@[expose] noncomputable def rowK (t : Nat) (U : Option Nat) (G : Nat → Nat) (ng : Nat) : Bool :=
  bAnd(isInvK 80 7 t, bAnd(Option.rec (motive := fun _ => Bool) (sP t) (fun u => sP (pc t u)) U,
    allN ng fun k => bAnd(sP (G k), cm (G k) t)))

theorem rows :
    rowK (K2106.T K2106.r0) none CD0.G CD0.ng = true ∧
    rowK (K1080.T K1080.r0) (some UD) CD1.G CD1.ng = true ∧
    rowK (K5265.T K5265.r0) none CD2.G CD2.ng = true ∧
    rowK (K2106.T K2106.r1) none CS0.G CS0.ng = true ∧
    rowK (K10530.T K10530.r0) (some US) CS1.G CS1.ng = true ∧
    rowK (K5265.T K5265.r1) none CS2.G CS2.ng = true ∧
    rowK (K117a.T K117a.r0) (some US) CS3.G CS3.ng = true ∧
    rowK (K117b.T K117b.r0) (some US) CS4.G CS4.ng = true ∧
    rowK (K5265.T K5265.r2) none CDS0.G CDS0.ng = true ∧
    rowK (K2106.T K2106.r2) none CDS1.G CDS1.ng = true ∧
    rowK (K8424.T K8424.r0) (some UDS) CDS2.G CDS2.ng = true := by
  decide +kernel

@[expose] noncomputable def normK (t : Nat) (G : Nat → Nat) (ng N : Nat) (T S : Nat → Nat)
    (C CI : Nat → Nat) (nc : Nat) : Bool :=
  bAnd(allN ng (fun k => bAnd(sP (G k), cm (G k) t)),
    allN nc fun c => allN ng fun k => memK 80 7 ps N T S (pc (C c) (pc (G k) (CI c))))

theorem smallK : normK (K5265.T K5265.r0) KD2.G KD2.ng KD2.N KD2.T KD2.S CD2.G CD2.GI CD2.ng =
    true := by
  decide +kernel

theorem fiveK :
    allN FS3.ng (fun k => bAnd(sP (FS3.G k), bAnd(cm (FS3.G k) (K117a.T K117a.r0),
      ord5K 80 7 (FS3.G k)))) = true ∧
    allN FS4.ng (fun k => bAnd(sP (FS4.G k), bAnd(cm (FS4.G k) (K117b.T K117b.r0),
      ord5K 80 7 (FS4.G k)))) = true := by
  decide +kernel

@[expose] noncomputable def diagK (D L Y : Nat) : Bool :=
  bAnd(allN 80 (fun i => Nat.beq (pg 7 (mask 7) D i) (pg 7 (mask 7) L i)),
    allN 6 fun i => Nat.beq (pg 7 (mask 7) D (Nat.add 80 i)) (Nat.add 80 (pg 3 (mask 3) Y i)))

theorem a6K :
    normK (K2106.T K2106.r0) LD0.G LD0.ng LD0.N LD0.T LD0.S CD0.G CD0.GI CD0.ng = true ∧
    normK (K8424.T K8424.r0) LDS2.G LDS2.ng LDS2.N LDS2.T LDS2.S CDS2.G CDS2.GI CDS2.ng = true ∧
    allN 2 (fun k => oddK 80 7 (LD0.G k)) = true ∧ allN 2 (fun k => oddK 80 7 (LDS2.G k)) = true ∧
    allN 2 (fun k => oddK 6 3 (A6.G k)) = true ∧
    LD0.ng = 2 ∧ LDS2.ng = 2 ∧ DD0.ng = 2 ∧ DDS2.ng = 2 ∧ A6.ng = 2 ∧
    allN 2 (fun k => diagK (DD0.G k) (LD0.G k) (A6.G k)) = true ∧
    allN 2 (fun k => diagK (DDS2.G k) (LDS2.G k) (A6.G k)) = true := by
  decide +kernel

@[expose] noncomputable def cosetK (t w : Nat) (U : Option Nat) (G : Nat → Nat) (ng : Nat) :
    Bool :=
  bAnd(cm w t, bAnd(sP (pc w w),
    bAnd(Option.rec (motive := fun _ => Bool) (sP w) (fun u => sP (pc w u)) U,
      allN ng fun k => bAnd(cm (G k) t, sP (G k) || sP (pc (G k) w)))))

@[expose] noncomputable def configK (mem : Nat → Bool) (L : Nat → Nat) (N : Nat) (T : Nat → Nat) :
    Bool :=
  allN N fun i => strictB (T i) fun v =>
    !isInvK 80 7 v || allN 360 (fun j => strictB (L j) fun l =>
      !(bAnd(isInvK 80 7 l, ord8K 80 7 (pc v l)))) || mem v

@[expose] noncomputable def wD1 : Nat := pk (e 29414775 false)
@[expose] noncomputable def wD2 : Nat := pk (e 25614936 true)
@[expose] noncomputable def wD3 : Nat := pk (e 24033253 true)
@[expose] noncomputable def wDS1 : Nat := pk (e 21158344 false)
@[expose] noncomputable def wDS2 : Nat := pk (e 7406221 true)
@[expose] noncomputable def wDS3 : Nat := pk (e 14204479 true)

theorem cosets :
    cosetK (K2106.T K2106.r0) (pidn 80 7) none TD00.G TD00.ng = true ∧
    cosetK (K2106.T K2106.r0) wD1 (some UD) TD01.G TD01.ng = true ∧
    cosetK (K2106.T K2106.r0) wD2 (some US) TD02.G TD02.ng = true ∧
    cosetK (K2106.T K2106.r0) wD3 (some UDS) TD03.G TD03.ng = true ∧
    cosetK (K8424.T K8424.r0) (pidn 80 7) none TDS20.G TDS20.ng = true ∧
    cosetK (K8424.T K8424.r0) wDS1 (some UD) TDS21.G TDS21.ng = true ∧
    cosetK (K8424.T K8424.r0) wDS2 (some US) TDS22.G TDS22.ng = true ∧
    cosetK (K8424.T K8424.r0) wDS3 (some UDS) TDS23.G TDS23.ng = true := by
  decide +kernel

theorem configD0 : configK good LD0.T TD00.N TD00.T = true := by decide +kernel
theorem configD1 : configK good LD0.T TD01.N TD01.T = true := by decide +kernel
theorem configD2 : configK good LD0.T TD02.N TD02.T = true := by decide +kernel
theorem configD3 : configK good LD0.T TD03.N TD03.T = true := by decide +kernel
theorem configDS0 : configK good LDS2.T TDS20.N TDS20.T = true := by decide +kernel
theorem configDS1 : configK good LDS2.T TDS21.N TDS21.T = true := by decide +kernel
theorem configDS2 : configK good LDS2.T TDS22.N TDS22.T = true := by decide +kernel
theorem configDS3 : configK good LDS2.T TDS23.N TDS23.T = true := by decide +kernel

end CertificateChecks.KernelP1L43

end
