(declare-fun a_ack!7 () (_ BitVec 64))
(declare-fun FPCHECK_FDIV_ACCURACY ((_ FloatingPoint 11 53) (_ BitVec 64)) Bool)
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!7)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (FPCHECK_FDIV_ACCURACY
  (fp.mul roundNearestTiesToEven
          ((_ to_fp 11 53) a_ack!7)
          ((_ to_fp 11 53) a_ack!7))
  #x4018000000000000))
