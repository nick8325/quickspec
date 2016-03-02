-- Inspired by Agda's undefined.h
#define __ ERROR("internal error")
#define ERROR(msg) (error (__FILE__ ++ ", line " ++ show (__LINE__ :: Int) ++ ": " ++ msg))
