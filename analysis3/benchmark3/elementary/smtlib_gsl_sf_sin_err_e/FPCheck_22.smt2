(declare-fun a_ack!39 () (_ BitVec 64))
(declare-fun FPCHECK_FMUL_UNDERFLOW
             ((_ FloatingPoint 11 53) (_ BitVec 64))
             Bool)
(declare-fun b_ack!38 () (_ BitVec 64))
(declare-fun CF_cos ((_ BitVec 64)) (_ FloatingPoint 11 53))
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!39)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (FPCHECK_FMUL_UNDERFLOW (CF_cos a_ack!39) b_ack!38))
