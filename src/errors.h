-- Inspired by Agda's undefined.h
#define __ (ERROR "no error message given")
#define ERROR (\msg -> error ("Error at file " ++ __FILE__ ++ ", line " ++ show __LINE__ ++ ": " ++ msg))
