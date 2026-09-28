"""Small synchronous CUDA Driver API adapter; no kernel arithmetic in Python."""
import ctypes as C


class Cuda:
    def __init__(self):
        self.lib = C.CDLL("libcuda.so.1")
        signatures = {
            "cuInit": [C.c_uint], "cuDeviceGet": [C.POINTER(C.c_int), C.c_int],
            "cuDevicePrimaryCtxRetain": [C.POINTER(C.c_void_p), C.c_int],
            "cuDevicePrimaryCtxRelease": [C.c_int], "cuCtxSetCurrent": [C.c_void_p],
            "cuCtxSynchronize": [],
            "cuDeviceGetAttribute": [C.POINTER(C.c_int), C.c_int, C.c_int],
            "cuDriverGetVersion": [C.POINTER(C.c_int)],
            "cuModuleLoad": [C.POINTER(C.c_void_p), C.c_char_p],
            "cuModuleUnload": [C.c_void_p],
            "cuModuleGetFunction": [C.POINTER(C.c_void_p), C.c_void_p, C.c_char_p],
            "cuMemAlloc_v2": [C.POINTER(C.c_uint64), C.c_size_t],
            "cuMemFree_v2": [C.c_uint64],
            "cuMemcpyHtoD_v2": [C.c_uint64, C.c_void_p, C.c_size_t],
            "cuMemcpyDtoH_v2": [C.c_void_p, C.c_uint64, C.c_size_t],
            "cuLaunchKernel": [C.c_void_p] + [C.c_uint]*7 + [C.c_void_p, C.POINTER(C.c_void_p), C.c_void_p],
            "cuGetErrorName": [C.c_int, C.POINTER(C.c_char_p)],
        }
        for name, args in signatures.items():
            fn = getattr(self.lib, name)
            fn.argtypes, fn.restype = args, C.c_int
        self.call("cuInit", 0)
        self.device = C.c_int()
        self.call("cuDeviceGet", C.byref(self.device), 0)
        self.context = C.c_void_p()
        self.call("cuDevicePrimaryCtxRetain", C.byref(self.context), self.device)
        self.call("cuCtxSetCurrent", self.context)

    def call(self, name, *args):
        result = getattr(self.lib, name)(*args)
        if result:
            text = C.c_char_p()
            self.lib.cuGetErrorName(result, C.byref(text))
            raise RuntimeError(f"{name}: {result} {text.value!r}")

    def attribute(self, number):
        value = C.c_int()
        self.call("cuDeviceGetAttribute", C.byref(value), number, self.device)
        return value.value

    def execute(self, cubin, words, rows, width, shared_bytes):
        if not rows:
            return list(words)
        if width > self.attribute(1) or shared_bytes > self.attribute(8) or rows > self.attribute(5):
            raise ValueError("launch exceeds device thread/shared-memory/grid limit")
        module, function, pointer = C.c_void_p(), C.c_void_p(), C.c_uint64()
        allocated = loaded = False
        try:
            self.call("cuModuleLoad", C.byref(module), str(cubin).encode())
            loaded = True
            self.call("cuModuleGetFunction", C.byref(function), module, b"dense_relu")
            # Allocation guard words detect writes immediately outside the logical arena.
            guards = [0xA5A55A5A]*16
            packet = guards + list(words) + guards
            host = (C.c_uint32*len(packet))(*packet)
            self.call("cuMemAlloc_v2", C.byref(pointer), C.sizeof(host))
            allocated = True
            self.call("cuMemcpyHtoD_v2", pointer, host, C.sizeof(host))
            base = C.c_uint64(pointer.value + 4*len(guards))
            params = (C.c_void_p*1)(C.cast(C.byref(base), C.c_void_p))
            self.call("cuLaunchKernel", function, rows, 1, 1, width, 1, 1, 0, None, params, None)
            self.call("cuCtxSynchronize")
            self.call("cuMemcpyDtoH_v2", host, pointer, C.sizeof(host))
            actual = list(host)
            if actual[:16] != guards or actual[-16:] != guards:
                raise AssertionError("kernel modified allocation guard words")
            return actual[16:-16]
        finally:
            if allocated:
                self.call("cuMemFree_v2", pointer)
            if loaded:
                self.call("cuModuleUnload", module)

    def close(self):
        self.call("cuDevicePrimaryCtxRelease", self.device)
