#include "org_example_antbook_cpu_CpuInfo.h"

JNIEXPORT jlong JNICALL
Java_org_example_antbook_cpu_CpuInfo_getCpuClock
(JNIEnv *,
 jobject) {

//  __int64 timestamp;
//  __int64 *pTimestamp=&timestamp;
//  _asm rdtsc;
//  _asm mov ecx,pTimestamp
//    _asm mov [ecx],eax;
//  _asm mov [ecx+4],edx;

  return 0;
}
