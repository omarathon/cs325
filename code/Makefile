CXX=clang++ -std=c++17
CFLAGS= -g -O3 `llvm-config --cxxflags --ldflags --system-libs --libs all` \
-Wno-unused-function -Wno-unknown-warning-option 

FLAGS_FOR_DCS_SYSTEMS=-stdlib=libstdc++ -cxx-isystem /local/java/gcc-9.2.0/include/c++/9.2.0/ -cxx-isystem /local/java/gcc-9.2.0/include/c++/9.2.0/x86_64-pc-linux-gnu/ -L/local/java/gcc-9.2.0/lib64 -L/local/java/gcc-9.2.0/lib/gcc/x86_64-pc-linux-gnu/9.2.0/  


mccomp: mccomp.cpp
	$(CXX) mccomp.cpp $(CFLAGS) $(FLAGS_FOR_DCS_SYSTEMS) -o mccomp

clean:
	rm -rf mccomp 
