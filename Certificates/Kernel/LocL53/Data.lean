module

public import Certificates.Data.Kernel.LocLn.Defs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL53.TT "Certificates/Kernel/LocL53/data/pts.bin"
  3 9
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095
  65536 7935343882592794524

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL53.OT "Certificates/Kernel/LocL53/data/tab.bin"
  6 4 65535 25742 4948280578957695469

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL53.CT "Certificates/Kernel/LocL53/data/cv.bin"
  6 5 4294967295 277888 8877803305120794566

#kc_repo #kc_blocked_root CertificateChecks.KernelLocL53.RP "Certificates/Kernel/LocL53/data/rep.bin"
  3 9
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095
  8576 11054157677305017792

namespace CertificateChecks.KernelLocL53

open CFSG.KD.LocLn

@[expose] noncomputable def G (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 10087068705184456109095925531356760208662616972162580592856997373052441090400499725484605408220600118515959947665145857,
  nIf(Nat.beq k 1, 10126470713729321499250296420591616478271911133838489504002194964057279805530279865420520837867111262600063574878585345,
  nIf(Nat.beq k 2, 10126315594821924020299783702027473703523938003381049953727941336638377308951314021791138674214632685795455227442233600,
  nIf(Nat.beq k 3, 10166026633994144186221011464093952257527845029452198931164839087590675798733829267864119199289224465592961249186938881,
  nIf(Nat.beq k 4, 20173827172554045028520770960629056930678801935888001047384577421959942265952950141607755184655332519160471542357426433,
  nIf(Nat.beq k 5, 10086913586277022514259309110631448801697808181052230732116306589415334515098768947772922494707403146339279873175977985,
    2582250032604570810047077534074686221902415427209512179823845473705302290074649231507241795140876932365748335290278347008))))))

@[expose] noncomputable def T (i : Nat) : Nat := TT i

@[expose] noncomputable def E (i k : Nat) : Nat := OT (Nat.add (Nat.mul 7 i) k)

@[expose] noncomputable def PA (i : Nat) : Nat := OT (Nat.add 7168 i)

@[expose] noncomputable def LA (i : Nat) : Nat := OT (Nat.add 8192 i)

@[expose] noncomputable def SO (i : Nat) : Nat := OT (Nat.add 9216 i)

@[expose] noncomputable def SOI (i : Nat) : Nat := OT (Nat.add 10240 i)

@[expose] noncomputable def F (i : Nat) : Nat := OT (Nat.add 11264 i)

@[expose] noncomputable def O8 (a : Nat) : Nat := OT (Nat.add 12288 a)

@[expose] noncomputable def O2 (b : Nat) : Nat := OT (Nat.add 12704 b)

@[expose] noncomputable def CV (c : Nat) : Nat := CT c

@[expose] noncomputable def RX (r : Nat) : Nat := RP r

@[expose] noncomputable def RT (r : Nat) : Nat := RP (Nat.add 67 r)

@[expose] noncomputable def l53Pt (q : Nat) : Bool :=
  blkN k5 7 1024 G T E PA LA SO SOI (Nat.mul 64 q) 64

@[expose] noncomputable def l53Fl (q : Nat) : Bool := flagBlk k5 T F (Nat.mul 64 q) 64

@[expose] noncomputable def l53Pr (q : Nat) : Bool :=
  pairBlk k5 1024 67 T O8 O2 CV RX RT 167 (Nat.mul 4 q) 4

end CertificateChecks.KernelLocL53

end
