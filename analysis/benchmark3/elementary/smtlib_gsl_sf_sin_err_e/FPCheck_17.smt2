(declare-fun a_ack!27 () (_ BitVec 64))
(declare-fun FPCHECK_FMUL_ACCURACY
             ((_ FloatingPoint 11 53) (_ FloatingPoint 11 53))
             Bool)
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!27)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (FPCHECK_FMUL_ACCURACY
  (fp.mul roundNearestTiesToEven
          ((_ to_fp 11 53) a_ack!27)
          (fp.mul roundNearestTiesToEven
                  ((_ to_fp 11 53) a_ack!27)
                  ((_ to_fp 11 53) a_ack!27)))
  (fp.mul roundNearestTiesToEven
          ((_ to_fp 11 53) a_ack!27)
          ((_ to_fp 11 53) a_ack!27))))
