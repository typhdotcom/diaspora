import os
import re

# Configuration
SOURCE_DIR = "Diaspora"

# These keywords generally start a new top-level block.
# If we are skipping a proof, hitting one of these at the start of a line (no indent)
# means the proof is over.
TOP_LEVEL_KEYWORDS = {
    "def", "structure", "class", "abbrev", "inductive",
    "theorem", "lemma", "example", "instance",
    "namespace", "section", "end", 
    "import", "open", "variable", "set_option", "#"
}

# These are the declarations we want to strip the bodies of.
# We KEEP the bodies of def/structure/instance because those are definitions.
PROOF_DECLARATIONS = {"theorem", "lemma", "example"}

def is_top_level_start(line):
    """Returns True if the line starts with a keyword that indicates a new declaration."""
    first_word = line.split(' ')[0]
    # Check for doc comments or attributes
    if line.startswith("/-") or line.startswith("@") or line.startswith("--"):
        return False
    return first_word in TOP_LEVEL_KEYWORDS

def clean_lean_file(content):
    lines = content.splitlines()
    output_lines = []
    
    # States
    # 'normal': reading imports, comments, defs, or looking for start of theorem
    # 'reading_sig': we found a theorem start, reading the type signature
    # 'skipping_proof': we found the proof start, discarding lines until next top-level
    state = 'normal'
    
    for line in lines:
        stripped = line.strip()
        
        # 1. Handle Skip Mode
        if state == 'skipping_proof':
            # If line is empty/whitespace, skip it
            if not stripped:
                continue
            # If we hit a new top-level keyword (0 indentation), stop skipping
            # We check len(line) - len(line.lstrip()) to ensure it is 0 indent.
            indent_level = len(line) - len(line.lstrip())
            if indent_level == 0 and is_top_level_start(stripped):
                state = 'normal'
                # Fall through to process this line as a normal line
            else:
                # Still in proof, skip
                continue

        # 2. Check for start of a Proof Declaration (theorem/lemma)
        first_word = stripped.split(' ')[0]
        if state == 'normal' and first_word in PROOF_DECLARATIONS:
            state = 'reading_sig'
        
        # 3. Handle Signature Reading
        if state == 'reading_sig':
            # Check for immediate proof start on this line
            
            # Case A: ":= by" (The most common standard)
            if ":= by" in line:
                # Keep everything before ":= by", add marker
                pre, _ = line.split(":= by", 1)
                output_lines.append(pre.rstrip() + " := ...")
                state = 'skipping_proof'
                continue

            # Case B: Line ends with ":=" (Proof starts on next line)
            if line.rstrip().endswith(":="):
                output_lines.append(line.rstrip() + " ...")
                state = 'skipping_proof'
                continue

            # Case C: Line starts with "by" (Proof start)
            if stripped.startswith("by "):
                # The previous line ended the sig. This line is garbage.
                # Remove the newline from previous if possible to make it look clean? 
                # actually just adding := ... to the previous line is hard here.
                # Let's just output ":= ..." on this line.
                output_lines.append(line.replace(stripped, ":= ..."))
                state = 'skipping_proof'
                continue
            
            # If we are here, it's just a line of the signature (arguments/types)
            output_lines.append(line)
            
            # Safety valve: if we hit a new top level while reading sig, something went wrong 
            # or the theorem has no body (axiom?). Reset.
            # (But only check if indentation is 0 to avoid false positives on args)
            indent = len(line) - len(line.lstrip())
            if indent == 0 and is_top_level_start(stripped) and first_word not in PROOF_DECLARATIONS:
                 state = 'normal'

        # 4. Handle Normal Mode (Defs, Comments, Structures)
        elif state == 'normal':
            output_lines.append(line)

    return "\n".join(output_lines)

def main():
    if not os.path.exists(SOURCE_DIR):
        print(f"Error: Directory '{SOURCE_DIR}' not found.")
        return

    print(f"/- DIASPORA PROJECT: SEMANTIC EXTRACT -/")
    print(f"/- Definitions are preserved. Theorem proofs are omitted. -/")
    print("")

    for root, dirs, files in os.walk(SOURCE_DIR):
        # simple sort to keep file order deterministic
        for file in sorted(files):
            if file.endswith(".lean"):
                full_path = os.path.join(root, file)
                
                print(f"/-- FILE: {full_path} --/")
                try:
                    with open(full_path, "r", encoding="utf-8") as f:
                        raw_content = f.read()
                        print(clean_lean_file(raw_content))
                except Exception as e:
                    print(f"/- Error reading file {full_path}: {e} -/")
                
                print("\n")

if __name__ == "__main__":
    main()
