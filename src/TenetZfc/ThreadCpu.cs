using System.Runtime.InteropServices;

namespace TenetZfc;

/// <summary>
/// The CPU time the calling thread has used, in seconds: for time budgets that a loaded machine doesn't shrink
/// (theorem-all). macOS through Mach's thread_info, Linux through clock_gettime(CLOCK_THREAD_CPUTIME_ID); elsewhere,
/// or if the call fails, null, and callers fall back to wall time.
/// </summary>
public static partial class ThreadCpu
{
    public static double? Seconds()
    {
        try
        {
            if (OperatingSystem.IsMacOS())
            {
                uint port = mach_thread_self();
                try
                {
                    // thread_basic_info: user_time {sec, usec}, system_time {sec, usec}, then six more ints.
                    var info = new int[10];
                    int count = 10;
                    if (thread_info(port, 3 /* THREAD_BASIC_INFO */, info, ref count) != 0)
                    {
                        return null;
                    }
                    return info[0] + info[1] / 1e6 + info[2] + info[3] / 1e6;
                }
                finally
                {
                    _ = mach_port_deallocate(mach_task_self_, port);
                }
            }
            if (OperatingSystem.IsLinux())
            {
                var ts = new long[2];
                return clock_gettime(3 /* CLOCK_THREAD_CPUTIME_ID */, ts) == 0 ? ts[0] + ts[1] / 1e9 : null;
            }
        }
        catch (Exception e) when (e is DllNotFoundException or EntryPointNotFoundException)
        {
        }
        return null;
    }

    [LibraryImport("libSystem.dylib")]
    private static partial uint mach_thread_self();

    [LibraryImport("libSystem.dylib")]
    private static partial int thread_info(uint thread, int flavor, [In, Out] int[] info, ref int count);

    [LibraryImport("libSystem.dylib")]
    private static partial int mach_port_deallocate(uint task, uint name);

    private static readonly uint mach_task_self_ = OperatingSystem.IsMacOS() ? TaskSelf() : 0;

    private static uint TaskSelf()
    {
        // mach_task_self() is a macro over the global mach_task_self_.
        IntPtr lib = NativeLibrary.Load("libSystem.dylib");
        return (uint)Marshal.ReadInt32(NativeLibrary.GetExport(lib, "mach_task_self_"));
    }

    [LibraryImport("libc", EntryPoint = "clock_gettime")]
    private static partial int clock_gettime(int clock, [In, Out] long[] ts);
}
