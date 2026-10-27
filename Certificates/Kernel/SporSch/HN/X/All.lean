module

public import Certificates.Kernel.SporSch.HN.X.C0
public import Certificates.Kernel.SporSch.HN.X.C1
public import Certificates.Kernel.SporSch.HN.X.C2
public import Certificates.Kernel.SporSch.HN.X.C3
public import Certificates.Kernel.SporSch.HN.X.C4
public import Certificates.Kernel.SporSch.HN.X.C5
public import Certificates.Kernel.SporSch.HN.X.C6
public import Certificates.Kernel.SporSch.HN.X.C7
public import Certificates.Kernel.SporSch.HN.X.C8
public import Certificates.Kernel.SporSch.HN.X.S0
public import Certificates.Kernel.SporSch.HN.X.S1
public import Certificates.Kernel.SporSch.HN.X.S2
public import Certificates.Kernel.SporSch.HN.X.S3
public import Certificates.Kernel.SporSch.HN.X.S4
public import Certificates.Kernel.SporSch.HN.X.S5
public import Certificates.Kernel.SporSch.HN.X.S6
public import Certificates.Kernel.SporSch.HN.X.S7
public import Certificates.Kernel.SporSch.HN.X.S8
public import CFSG.Certificates.Kernel.Common.ForallBlocks

public section

namespace CFSG.KD.HNXK

open CFSG.KC.ForallBlocks

theorem core_all : ∀ q < 17813, coreOk q = true :=
  forall_of_blocks (R := 2048) (G := 9) (by decide) (by decide) fun j hj =>
    match j, hj with
    | 0, _ => fun i hi _ => C0.all i hi
    | 1, _ => fun i hi _ => C1.all i hi
    | 2, _ => fun i hi _ => C2.all i hi
    | 3, _ => fun i hi _ => C3.all i hi
    | 4, _ => fun i hi _ => C4.all i hi
    | 5, _ => fun i hi _ => C5.all i hi
    | 6, _ => fun i hi _ => C6.all i hi
    | 7, _ => fun i hi _ => C7.all i hi
    | 8, _ => fun i _ h => C8.all i (by change i < 1429; omega)
    | _ + 9, h => absurd h (by omega)

theorem sort_all : ∀ q < 17813, sortOk q = true :=
  forall_of_blocks (R := 2048) (G := 9) (by decide) (by decide) fun j hj =>
    match j, hj with
    | 0, _ => fun i hi _ => S0.all i hi
    | 1, _ => fun i hi _ => S1.all i hi
    | 2, _ => fun i hi _ => S2.all i hi
    | 3, _ => fun i hi _ => S3.all i hi
    | 4, _ => fun i hi _ => S4.all i hi
    | 5, _ => fun i hi _ => S5.all i hi
    | 6, _ => fun i hi _ => S6.all i hi
    | 7, _ => fun i hi _ => S7.all i hi
    | 8, _ => fun i _ h => S8.all i (by change i < 1429; omega)
    | _ + 9, h => absurd h (by omega)

end CFSG.KD.HNXK

end
