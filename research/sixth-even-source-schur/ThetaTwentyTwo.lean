import ThetaTwenty
import AllOrderPattern

/-! The unchanged infinite theta source on the unchanged grid. Only the
weight order is extended; the three retained tails and ALL omitted modes
remain in the enclosure. Narrow witnesses below are verified by the kernel. -/
namespace CarrySixthEven
open CarryIntegralCertificate CarrySelfAdjointOperator Real Set Filter MeasureTheory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem mem_tabledTheta_upto_twentyTwo (p : ℕ) (hp : p ≤ 22) :
    (tabledFullThetaMomentBox p).Mem (completedNativeThetaTailMoment p) := by
  have hpR : (p:ℝ) ≤ 22 := by exact_mod_cast hp
  have hd0 := thetaArgument_coarse_lower 0 (by norm_num : (0:ℝ) ≤ 96/64)
  have hd1 := thetaArgument_coarse_lower 1 (by norm_num : (0:ℝ) ≤ 64/64)
  have hd2 := thetaArgument_coarse_lower 2 (by norm_num : (0:ℝ) ≤ 48/64)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hd0 hd1 hd2
  have hm0 := mem_exactFullModeBox (0:Fin 3) 15 p (by omega)
    (by norm_num [thetaCertificateCellCount]) (by
      norm_num only [Fin.val_zero,thetaCertificateCellCount] at hd0 ⊢
      nlinarith only [hd0,hpR])
  have hm1 := mem_exactFullModeBox (1:Fin 3) 15 p (by omega)
    (by norm_num [thetaCertificateCellCount]) (by
      norm_num [thetaCertificateCellCount] at hd1 ⊢
      nlinarith only [hd1,hpR])
  have hm2 := mem_exactFullModeBox (2:Fin 3) 15 p (by omega)
    (by norm_num [thetaCertificateCellCount]) (by
      norm_num [thetaCertificateCellCount] at hd2 ⊢
      nlinarith only [hd2,hpR])
  have hb := integral_weightedOmittedModes_bounds p
  have hr := mem_outer (mem_point 0)
    (mem_rat p.factorial ((10:ℤ)^20*95^(p+1)))
    (by simpa only [Int.cast_zero] using hb.1) (by
      simpa only [Int.cast_natCast,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using hb.2)
  have hx := mem_add (mem_add (mem_add hm0 hm1) hm2) hr
  rw [completedNativeThetaTailMoment_eq_three_and_remainder p]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceAdd]
  rw [← exactFullThetaMomentBox_eq_tabled]
  exact hx

def thetaInputTable : Fin 12 → Box := ![Box.finite (11516887246743560348732755885386023825365752730758657403552) (11516887246743560349107632458619016547804327699490440633795),
  Box.finite (247320713366732650218888207553216440309995835363966474777) (247320713366732650260769199070835817424796894371457623678),
  Box.finite (20000506852638550076037466756835634254483291446041846211) (20000506852638550096482554980811812908251540555248643010),
  Box.finite (2877035926308042983185119722033841071043091400439842539) (2877035926308042995699089113530972915557840327052945228),
  Box.finite (589749292219186094799812402117159047862035175816521791) (589749292219186103394300681901526879103672273339067944),
  Box.finite (155208085744376563098905276136334372755216690394222651) (155208085744376569526372791714765725521798275281862303),
  Box.finite (49408429981963264164190416302552625482700418525936077) (49408429981963269320776167843954684379635998514037073),
  Box.finite (18313453794899136218543688905675004410052567891527988) (18313453794899140613950680345462930472181489253269031),
  Box.finite (7698639471708823099101073475094839720571776721026653) (7698639471708827052965003109631287365615370683633564),
  Box.finite (3601179054917292764756466741123947291570533491872573) (3601179054917296501180986022381506047165138245478998),
  Box.finite (1847557118783259200662925591603197391278254492293871) (1847557118783262901608147885524594521884392396975721),
  Box.finite (1027990835141850801121369832708422759032584559450055) (1027990835141854646103370792330136360197443933428540)]

def thetaInputBox (n : ℕ) : Box := if h : n < 12 then thetaInputTable ⟨n,h⟩ else .all

end CarrySixthEven
