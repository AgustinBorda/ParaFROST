/***********************************************************************[solve.cpp]
Copyright(c) 2020, Muhammad Osama - Anton Wijs,
Technische Universiteit Eindhoven (TU/e).

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
**********************************************************************************/

#include "solve.h" 

#if defined(__linux__)
#include <fpu_control.h>
#endif

namespace ParaFROST {

	int64 sysMemUsed()
	{
		int64 memUsed = 0;
#if defined(__linux__) || defined(__CYGWIN__)
		FILE* file = fopen("/proc/self/status", "r");
		char line[128];
		uint32 sign = 0;
		while (fgets(line, 128, file) != NULL) {
			char* str = line;
			if (eq(str, "VmRSS:")) {
				eatWS(str);
				memUsed = toInteger(str, sign);
				break;
			}
		}
		fclose(file);
		return memUsed * KBYTE;
#elif defined(_WIN32)
		PROCESS_MEMORY_COUNTERS_EX memInfo;
		GetProcessMemoryInfo(GetCurrentProcess(), (PROCESS_MEMORY_COUNTERS*)&memInfo, sizeof(PROCESS_MEMORY_COUNTERS_EX));
		memUsed = memInfo.WorkingSetSize;
#endif
		return memUsed;
	}

	int64 getAvailSysMem()
	{
#if defined(__linux__) || defined(__CYGWIN__)
		long pages = sysconf(_SC_PHYS_PAGES);
		long page_size = sysconf(_SC_PAGE_SIZE);
		return pages * page_size;
#elif defined(_WIN32)
		MEMORYSTATUSEX memInfo;
		memInfo.dwLength = sizeof(MEMORYSTATUSEX);
		GlobalMemoryStatusEx(&memInfo);
		return memInfo.ullAvailPhys;
#endif
	}

	void set_timeout(int time_limit)
	{
#if defined(__linux__) || defined(__CYGWIN__)
		if (time_limit) {
			rlimit limit;
			getrlimit(RLIMIT_CPU, &limit);
			if (limit.rlim_max == RLIM_INFINITY || (rlim_t)time_limit < limit.rlim_max) {
				limit.rlim_cur = time_limit;
				if (setrlimit(RLIMIT_CPU, &limit) == -1) PFLOGW("timeout cannot be set");
			}
		}
#elif defined(_WIN32)
		PFLOGW("timeout not supported on Windows");
#endif
	}

	void set_memoryout(int memory_limit)
	{
#if defined(__linux__)
		if (memory_limit) {
			rlim64_t limitbytes = (rlim64_t)memory_limit * GBYTE;
			rlimit64 limit;
			getrlimit64(RLIMIT_AS, &limit);
			if (limit.rlim_max == RLIM_INFINITY || limitbytes < limit.rlim_max) {
				limit.rlim_cur = limitbytes;
				if (setrlimit64(RLIMIT_AS, &limit) == -1) PFLOGW("memoryout cannot be set");
			}
		}
#elif defined(__CYGWIN__)
		if (memory_limit) {
			rlim_t limitbytes = (rlim_t)memory_limit * GBYTE;
			rlimit limit;
			getrlimit(RLIMIT_AS, &limit);
			if (limit.rlim_max == RLIM_INFINITY || limitbytes < limit.rlim_max) {
				limit.rlim_cur = limitbytes;
				if (setrlimit(RLIMIT_AS, &limit) == -1) PFLOGW("memoryout cannot be set");
			}
		}
#elif defined(_WIN32)
		PFLOGW("memoryout not supported on Windows");
#endif
	}

	void forceFPU()
	{
#if defined(__linux__) && defined(_FPU_EXTENDED) && defined(_FPU_DOUBLE)
		fpu_control_t cw = (_FPU_DEFAULT & ~_FPU_EXTENDED) | _FPU_DOUBLE;
		_FPU_SETCW(cw);
		PFLOG2(1, " Forced FPU to use %sdouble precision%s", CREPORTVAL, CNORMAL);
#endif 
	}

	void handler_terminate(int)
	{
		fflush(stdout);
		PFLOGS("UNKNOWN");
		_exit(EXIT_FAILURE);
	}

	void handler_mercy_interrupt(int)
	{
		fflush(stdout);
		solver->interrupt();
	}

	void handler_mercy_timeout(int)
	{
		fflush(stdout);
		solver->interrupt();
	}

	void signal_handler(void h_intr(int), void h_timeout(int))
	{
		signal(SIGINT, h_intr);
		signal(SIGTERM, h_intr);
#ifdef SIGXCPU
		if (h_timeout != NULL) signal(SIGXCPU, h_timeout);
#endif
	}

	void segmentation_fault(int)
	{
		fflush(stdout);
		PFLOGEN("segmentation fault detected.");
		_exit(EXIT_FAILURE);
	}

	void illegal_code(int)
	{
		fflush(stdout);
		PFLOGEN("illegal code detected.");
		_exit(EXIT_FAILURE);
	}

	void arithmetic_error(int)
	{
		fflush(stdout);
		PFLOGEN("arithmetic flaw detected.");
		_exit(EXIT_FAILURE);
	}

	void getCPUInfo(uint64& _free)
	{
	}

	void getBuildInfo()
	{
	}

}

void ParaFROST::Solver::killSolver()
{
	wrapup();
	PFLOG0("");
	PFLOGN2(1, " Cleaning up..");
	this->~Solver();
	solver = NULL;
	PFLDONE(1, 5);
	if (!quiet_en) PFLRULER('-', RULELEN);
	exit(EXIT_SUCCESS);
}
