#ifndef X86FRAME_H
#define X86FRAME_H

#include "frame.h"

Temp_temp F_eax();
Temp_temp F_ebx();
Temp_temp F_ecx();
Temp_temp F_edx();
Temp_temp F_esp();
Temp_temp F_ebp();
Temp_temp F_esi();
Temp_temp F_edi();

Temp_tempList F_callerSaveRegs();
#endif
