module

public import Certificates.Kernel.NT44.Pack
public import Certificates.Data.Kernel.Misc.RowsBind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KC.Misc.ArrEnum

theorem nt44_ks : rowsBind 2688 12 nt44KS ((ks ()).toList.map Array.toList) 0 = true := by
  simp only [ks, List.toList_toArray, List.map_cons, List.map_nil, ksRow000, ksRow001,
    Array.toList_append]
  quickRfl

theorem nt44_p0 : rowsBind 2688 12 nt44P0 ((p0 ()).toList.map Array.toList) 0 = true := by
  simp only [p0, List.toList_toArray, List.map_cons, List.map_nil, p0Row000, p0Row001, p0Row002,
    p0Row003, p0Row004, p0Row005, p0Row006, p0Row007, p0Row008, Array.toList_append]
  quickRfl

theorem nt44_sk : rowsBind 448 9 nt44SK ((sk ()).toList.map Array.toList) 0 = true := by
  quickRfl

theorem nt44_sp : rowsBind 448 9 nt44SP ((sp ()).toList.map Array.toList) 0 = true := by
  quickRfl

theorem nt44_lifts : rowsBind 2688 12 nt44L ((lifts ()).toList.map Array.toList) 0 = true := by
  simp only [lifts, Array.toList_append, List.toList_toArray, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil,
    liftRow000, liftRow001, liftRow002, liftRow003, liftRow004, liftRow005, liftRow006, liftRow007,
    liftRow008, liftRow009, liftRow010, liftRow011, liftRow012, liftRow013, liftRow014, liftRow015,
    liftRow016, liftRow017, liftRow018, liftRow019, liftRow020, liftRow021, liftRow022, liftRow023,
    liftRow024, liftRow025, liftRow026, liftRow027, liftRow028, liftRow029, liftRow030, liftRow031,
    liftRow032, liftRow033, liftRow034, liftRow035, liftRow036, liftRow037, liftRow038, liftRow039,
    liftRow040, liftRow041, liftRow042, liftRow043, liftRow044, liftRow045, liftRow046, liftRow047,
    liftRow048, liftRow049, liftRow050, liftRow051, liftRow052, liftRow053, liftRow054, liftRow055,
    liftRow056, liftRow057, liftRow058, liftRow059, liftRow060, liftRow061, liftRow062, liftRow063,
    liftRow064, liftRow065, liftRow066, liftRow067, liftRow068, liftRow069, liftRow070, liftRow071,
    liftRow072, liftRow073, liftRow074, liftRow075, liftRow076, liftRow077, liftRow078, liftRow079,
    liftRow080, liftRow081, liftRow082, liftRow083, liftRow084, liftRow085, liftRow086, liftRow087,
    liftRow088, liftRow089, liftRow090, liftRow091, liftRow092, liftRow093, liftRow094, liftRow095,
    liftRow096, liftRow097, liftRow098, liftRow099, liftRow100, liftRow101, liftRow102, liftRow103,
    liftRow104, liftRow105, liftRow106, liftRow107, liftRow108, liftRow109, liftRow110, liftRow111,
    liftRow112, liftRow113, liftRow114, liftRow115, liftRow116, liftRow117, liftRow118, liftRow119,
    liftRow120, liftRow121, liftRow122, liftRow123, liftRow124, liftRow125, liftRow126, liftRow127,
    liftRow128, liftRow129, liftRow130, liftRow131, liftRow132, liftRow133, liftRow134, liftRow135,
    liftRow136, liftRow137, liftRow138, liftRow139, liftRow140, liftRow141, liftRow142, liftRow143,
    liftRow144, liftRow145, liftRow146, liftRow147, liftRow148, liftRow149, liftRow150, liftRow151,
    liftRow152, liftRow153, liftRow154, liftRow155, liftRow156, liftRow157, liftRow158, liftRow159,
    liftRow160, liftRow161, liftRow162, liftRow163, liftRow164, liftRow165, liftRow166, liftRow167,
    liftRow168, liftRow169, liftRow170, liftRow171, liftRow172, liftRow173, liftRow174, liftRow175,
    liftRow176, liftRow177, liftRow178, liftRow179, liftRow180, liftRow181, liftRow182, liftRow183,
    liftRow184, liftRow185, liftRow186, liftRow187, liftRow188, liftRow189, liftRow190, liftRow191,
    liftRow192, liftRow193, liftRow194, liftRow195, liftRow196, liftRow197, liftRow198, liftRow199,
    liftRow200, liftRow201, liftRow202, liftRow203, liftRow204, liftRow205, liftRow206, liftRow207,
    liftRow208, liftRow209, liftRow210, liftRow211, liftRow212, liftRow213, liftRow214, liftRow215,
    liftRow216, liftRow217, liftRow218, liftRow219, liftRow220, liftRow221, liftRow222, liftRow223,
    liftRow224, liftRow225, liftRow226, liftRow227, liftRow228, liftRow229, liftRow230, liftRow231,
    liftRow232, liftRow233, liftRow234, liftRow235, liftRow236, liftRow237, liftRow238, liftRow239,
    liftRow240, liftRow241, liftRow242, liftRow243, liftRow244, liftRow245, liftRow246, liftRow247,
    liftRow248, liftRow249, liftRow250, liftRow251, liftRow252, liftRow253, liftRow254, liftRow255,
    Array.toList_append]
  quickRfl

end CertificateChecks.KernelNT44

end
