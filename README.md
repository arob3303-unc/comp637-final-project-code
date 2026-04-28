# UltimateAntiCheat: Formal Verification Analysis

![SampleOutput](https://github.com/AlSch092/UltimateAntiCheat/assets/94417808/8e2112b8-2c82-4a38-aca8-ec54aa7d7516)

## Overview

This repository contains a **formal security analysis** of [UltimateAntiCheat](https://github.com/AlSch092/UltimateAntiCheat), an open-source usermode anti-cheat system written in C++ for x64 Windows platforms. Rather than analyzing the full C++ implementation, this project uses **formal verification in Alloy** to mathematically verify that the anti-cheat's core detection mechanisms work as intended. By abstracting the source code into relational state-transition models, we perform automated SAT-based model checking to evaluate whether malicious runtime conditions are correctly detected and recorded.

## Formal Model Architecture

The `formal-model/` directory contains five independent formal verification models, each abstracting a distinct anti-cheat detection mechanism. These models are designed following a systematic abstraction process: backward slicing from source-level flag generation points, state booleanization, and transition abstraction. Each model preserves only the security-relevant behavior while omitting implementation details such as byte-level checksums, exact memory addresses, and Windows API mechanics.

### Model Files and Purposes

#### 1. **code-section-integrity.als**
This model verifies that **runtime modifications to protected code sections are detected**. It abstracts the `Integrity::PeriodicIntegrityCheck` routine, which computes checksums of critical executable sections (`.text`, `.rdata`). The model captures three security-relevant states: whether the protected section has been modified by an attacker, whether the checksum verification check has run, and whether a violation has been recorded. The main property verifies: *if the protected section is modified AND the integrity check runs, then a checksum violation must be recorded*.

**Security guarantee:** Code tampering cannot occur without detection.

#### 2. **debugger-attachment-detection.als**
This model verifies that **attached debuggers are consistently detected**. It abstracts the `AntiDebug::CheckForDebugger` routine, which monitors for debugger attachment through Windows APIs such as `IsDebuggerPresent`, `CheckRemoteDebuggerPresent`, and PEB flag inspection. The model tracks whether a debugger is attached, whether the debugger check has executed, and whether a detection flag has been recorded. The main property asserts: *if a debugger is attached AND the debugger check runs, then the detection must be recorded*.

**Security guarantee:** Debugger-assisted memory modification cannot proceed undetected.

#### 3. **unauthorized-module-mapping.als**
This model verifies that **suspicious executable memory regions outside known loaded modules are flagged**. It abstracts `Detections::DetectManualMapping`, which scans committed executable memory and identifies regions that are not part of legitimate loaded modules. The model includes boolean flags for region properties (committed, executable, in known module) and detection markers (PE header present, erased header heuristic matched). The main property checks: *if a suspicious manually-mapped region exists AND the monitor check runs, then the MANUAL_MAPPING flag must be recorded*.

**Security guarantee:** Injected or manually-mapped code cannot hide from detection.

#### 4. **memory-protection-violation.als**
This model verifies that **protected sections made writable are detected**. It abstracts page protection checks from `Detections::FindWritableAddress`, which queries memory protection flags to ensure critical sections remain read-only or execute-only. The model tracks whether a protected section has been made writable and whether the protection check has recorded the violation. The main property verifies: *if the protected section is writable AND the protection check runs, then the PAGE_PROTECTIONS flag must be recorded*.

**Security guarantee:** Memory protection bypass attempts are detected.

#### 5. **callback-structure-integrity.als**
This model verifies that **modifications to Thread Local Storage (TLS) callback structures are detected**. It abstracts `Integrity::IsTLSCallbackStructureModified`, which monitors the TLS callback chain in the PE header. TLS callbacks execute automatically during thread creation, making them a high-value attack vector for early code injection. The model captures whether the TLS structure has been modified and whether the integrity check has recorded the tampering. The main property ensures: *if the TLS callback structure is modified AND the TLS check runs, then the CODE_INTEGRITY flag must be recorded*.

**Security guarantee:** TLS injection attacks cannot evade detection.

### Combined Model

**ALL-MODELS-BELOW-COMBINED-IN-ONE-FILE.als** integrates all five mechanisms into a single unified state-transition system. This combined model allows verification of how the detection mechanisms interact when operating together in the same process. It uses frame predicates to ensure that each mechanism's transitions update only its relevant state variables, preserving the verified guarantees from the individual models while enabling cross-mechanism property analysis.

## Verification Results

All five detection mechanism models successfully pass formal verification at scope 6 (bounded traces of up to 6 states). **No counterexamples were produced**, indicating that each mechanism correctly records violations when its preconditions are met.

| Model File | Main Property | Result | Counter-example |
|---|---|---|---|
| `code-section-integrity.als` | CodeSectionModificationDetected | **Pass** | No |
| `debugger-attachment-detection.als` | DebuggerAttachmentDetected | **Pass** | No |
| `unauthorized-module-mapping.als` | UnauthorizedModuleMappingDetected | **Pass** | No |
| `memory-protection-violation.als` | MemoryProtectionViolationDetected | **Pass** | No |
| `callback-structure-integrity.als` | CallbackStructureIntegrityViolationDetected | **Pass** | No |

These results provide formal assurance that the UltimateAntiCheat system's detection logic is **sound at the component level**: each mechanism correctly identifies its target threat when given the opportunity to run.

## Abstraction Methodology

Each model follows eight abstraction rules to balance security fidelity with computational tractability:

1. **Flag-point backward slicing** – Start from source-level flagging points (e.g., `EvidenceLocker::AddFlagged`) and trace backward to identify necessary state variables.
2. **State booleanization** – Represent complex runtime facts as boolean state variables (e.g., `protectedSectionModified`).
3. **Transition abstraction** – Collapse multi-step source computations into single logical transitions.
4. **Pipeline preservation** – Maintain the causal structure: attacker action → detection check → recorded flag.
5. **Source-faithful check grouping** – Group checks according to source code structure.
6. **Evidence persistence** – Once a flag is recorded, it persists (matching source-level evidence accumulation).
7. **Implementation-artifact omission** – Omit details that don't affect security outcomes (exact algorithms, APIs, addresses).
8. **No fairness assumption** – Properties are conditional: *if* the bad condition exists *and* the check runs, *then* the flag is recorded.

## How to Run the Models

### Prerequisites
- **Alloy Analyzer** (latest version, available at [alloytools.org](https://alloytools.org))
- Any Alloy configuration (no special setup required)

### Running a Model
1. Open the Alloy Analyzer
2. Load one of the `.als` files from the `formal-model/` directory
3. Click **Execute** to run the checks
4. Review the results:
   - **No counterexample** = property verified ✓
   - **Counterexample generated** = property violated ✗

### Example: Verifying Code Section Integrity
```bash
# Load the model
open code-section-integrity.als

# Execute all checks
check CodeSectionModificationDetected for 6
```

## Threat Model Scope

These models verify detection of the following **usermode attacks**:

- Modifying protected code/data sections (detected by checksum mismatch)
- Attaching a debugger to the process
- Manually mapping executable memory outside known modules
- Changing page protections on critical sections
- Modifying TLS callback structures for code injection

**Out of scope:** kernel-level attacks, hardware attacks, remote exploitation, and fairness-based scheduling guarantees.

## Research Contribution

This formal verification approach provides **mathematically grounded assurance** that UltimateAntiCheat's detection logic is sound. Unlike traditional manual testing and code inspection, formal verification exhaustively explores all possible state sequences within the model, providing a level of rigor that is essential for high-assurance security systems. The absence of counterexamples demonstrates component-level correctness while highlighting opportunities for future work: modeling enforcement guarantees, scheduler fairness, and end-to-end detection pipelines.

---

# UltimateAntiCheat: A usermode anti-cheat built in C++ (x64)

![C++](https://img.shields.io/badge/c++-%2300599C.svg?style=for-the-badge&logo=c%2B%2B&logoColor=white)
![Visual Studio](https://img.shields.io/badge/Visual%20Studio-5C2D91.svg?style=for-the-badge&logo=visual-studio&logoColor=white)
![Windows](https://img.shields.io/badge/Windows-0078D6?style=for-the-badge&logo=windows&logoColor=white)
![Version](https://img.shields.io/badge/2.1-999999?style=flat-square&logo=Version&label=Version&labelColor=333333)

UltimateAntiCheat is an open source usermode anti-cheat system made to detect and prevent common attack vectors of game hacking. The project also features an optional client-server mechanism, with a heartbeat being sent every minute to clients. No privacy-invasive techniques are used. Optionally, a hybrid kernelmode + usermode approach can now be used through the settings in `main.cpp` and `Common/Settings.hpp` (you will need to make/provide your own driver for this).

The project now supports CMake & using the LLVM/clang-cl compiler, which can be found in the `llvm-clang` branch (may not always be up to date with main branch). In the future we will attempt to add in code obfuscation via LLVM transformative passes. Certain sections of the code such as the `Detections` class may be messy or lacking modularity since the project originally used C, then switched over to C++ later on. If you're looking for a lighter-weight library with much cleaner code, check out [UltimateDRM](https://github.com/AlSch092/UltimateDRM), and a much improved detection engine can be found at: [DetectionEngine](https://github.com/AlSch092/DetectionEngine)  

## Goals & Overview
   The main goal is to provide a reference point for educational purposes, rather than be commercial software. The project includes many fundamental and novel detection techniques, and aims to cover as many attack surfaces as possible (while being limited by usermode) such that an attacker is not able to gain a foothold from usermode into our process without being detected. Any modification to a single aspect will lead to being detected, for example: if someone tries to debug our code from usermode, they will likely re-map and change the page protections in order to perform memory edits to try and patch over debugger detections, which leads to their memory edit and remapping being detected. It's recommended that if possible you run an obfuscator on the compiled binary or IR for added security through obscurity. The project should be integrated to your game or software directly as source code instead of a standalone DLL in order to avoid DLL proxying/spoofing attacks, and a .lib build configuration is now supported.  

   If there is anything not working for you (throws unhandled exceptions, can't build, etc) please raise an issue and I will answer it ASAP. If you have code suggestions or techniques you'd like to see added, or want assistance with adding anti-cheat to your game, please send me an email. Anyone is welcome to contribute as long as your contribution is to the same standard and formatting as the existing codebase, and your code has been regression tested. More techniques and better design will be added to the project over time, and the file `changelog.md` contains a dated updates list. Visual Studio 2022 is used as the primary IDE, and it's recommended you use it for project viewing and compilation.  

## Current detections and preventions: 
For a list of current detections and preventions, please view the Wiki page (or click [here](https://github.com/AlSch092/UltimateAntiCheat/wiki/Detections-&-Preventions)).  

## Enabling/Disabling Networking:
Networking support is available in the project: the server can be found in the `Server` folder as its own project solution. Using networking is optional, and can be turned on/off through the variable `bool bNetworkingAvailable` in the file `main.cpp` (as part of the `Settings` class). If you choose to use networking, please follow the instructions in the README.md file in the server folder.  

## Windows version targeting:

The preprocessor definition `_WIN32_WINNT=0x...` can be used to target different versions of Windows at compile-time. For example, using 0x0A00 will target Windows 10 and above, and 0x0601 will target Windows 7 and above. Certain features might only work on newer Windows versions and are excluded from compilation based on this value. The client will also fetch the machine's windows version at program startup, in `main.cpp`.

## Licensing  

The GNU Affero general public license is used in this project. Please be aware of what you can and cannot do with this license: for example, you **do not** have permission to rip this project into your own commercial project or use this project in your own code base without it being open source. You **do** have permission to use this project if your project is also open source. Using this project for a "private game server" or any other stolen code/binaries automatically violates the license, and makes you liable for IP-related damages. If you desperately need to use the project for your closed-source game, email me instead of ripping the code and breaking the license.

## Class Flow Diagram

Each bold line indicates the above class holds an object or pointer of the bottom class. Shared classes are generally stored as a `shared_ptr` in code, and inheritance is currently only used in the `DebuggerDetections` class. Only important classes relevant to core functionality are shown in the diagram:

![ClassDiagram](https://github.com/user-attachments/assets/1b1ea458-93dd-4e6e-a4c1-ab9f6c3cf96e)
