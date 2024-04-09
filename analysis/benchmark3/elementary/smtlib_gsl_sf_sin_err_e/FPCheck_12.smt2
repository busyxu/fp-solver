(declare-fun a_ack!18 () (_ BitVec 64))
(declare-fun FPCHECK_FMUL_OVERFLOW ((_ BitVec 64) (_ FloatingPoint 11 53)) Bool)
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!18)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (FPCHECK_FMUL_OVERFLOW
  a_ack!18
  (fp.mul roundNearestTiesToEven
          ((_ to_fp 11 53) a_ack!18)
          ((_ to_fp 11 53) a_ack!18))))
