/* Asef Abdul Awal Khan-2111468042
 * Hasan Mohammad Abdul Quadir-2312411042
 * Badrul Hassan Sadman-2413903042
 * Sumit Hawlader-2413307042
 */
import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class Assembler {

    private static final Pattern LEADING_LABEL = Pattern.compile(
            "^([A-Za-z_][A-Za-z0-9_]*)\\s*:"
    );

    private static final Pattern MEMORY_OPERAND = Pattern.compile(
            "^([+-]?(?:0[xX][0-9A-Fa-f]+|0[bB][01]+|[0-9]+))\\s*\\(\\s*([^()]+)\\s*\\)$"
    );

    private static final Map<String, Integer> OPCODES = createOpcodeTable();
    private static final Map<String, Integer> REGISTERS = createRegisterTable();

    private Assembler() {
        
    }

    public static void main(String[] args) {
        if (args.length < 1 || args.length > 2) {
            printUsage();
            System.exit(1);
        }

        Path inputPath = Paths.get(args[0]);
        Path outputPath = args.length == 2
                ? Paths.get(args[1])
                : Paths.get("output.txt");

        try {
            assemble(inputPath, outputPath);
            System.out.println("Assembly completed successfully.");
            System.out.println("Output file: " + outputPath.toAbsolutePath());
        } catch (AssemblyException e) {
            System.err.println("Assembly failed: " + e.getMessage());
            System.exit(1);
        } catch (IOException e) {
            System.err.println("File error: " + e.getMessage());
            System.exit(1);
        }
    }

    private static void printUsage() {
        System.out.println("Usage: java Assembler <input.asm> [output.txt]");
    }

    
    public static void assemble(Path inputPath, Path outputPath)
            throws IOException, AssemblyException {

        List<String> sourceLines = Files.readAllLines(inputPath, StandardCharsets.UTF_8);
        Map<String, Integer> labels = new HashMap<String, Integer>();
        List<SourceInstruction> instructions = new ArrayList<SourceInstruction>();

        firstPass(sourceLines, labels, instructions);
        List<Integer> machineWords = secondPass(labels, instructions);
        writeHexOutput(outputPath, machineWords);
    }

    private static void firstPass(
            List<String> sourceLines,
            Map<String, Integer> labels,
            List<SourceInstruction> instructions
    ) throws AssemblyException {

        int instructionAddress = 0;

        for (int i = 0; i < sourceLines.size(); i++) {
            int sourceLineNumber = i + 1;
            String line = sourceLines.get(i);

            
            if (i == 0 && !line.isEmpty() && line.charAt(0) == '\uFEFF') {
                line = line.substring(1);
            }

            line = stripComment(line).trim();
            if (line.isEmpty()) {
                continue;
            }

            
            while (true) {
                Matcher matcher = LEADING_LABEL.matcher(line);
                if (!matcher.find()) {
                    break;
                }

                String originalLabel = matcher.group(1);
                String labelKey = normalizeLabel(originalLabel);

                if (labels.containsKey(labelKey)) {
                    throw error(sourceLineNumber,
                            "Duplicate label '" + originalLabel + "'.");
                }

                labels.put(labelKey, instructionAddress);
                line = line.substring(matcher.end()).trim();

                if (line.isEmpty()) {
                    break;
                }
            }

            if (line.isEmpty()) {
                continue;
            }

            if (line.indexOf(':') >= 0) {
                throw error(sourceLineNumber,
                        "Invalid label syntax near ':'. Labels must appear at the beginning of a line.");
            }

            instructions.add(new SourceInstruction(
                    instructionAddress,
                    sourceLineNumber,
                    line
            ));
            instructionAddress++;
        }
    }

    private static List<Integer> secondPass(
            Map<String, Integer> labels,
            List<SourceInstruction> instructions
    ) throws AssemblyException {

        List<Integer> machineWords = new ArrayList<Integer>();

        int instructionCount = instructions.size();

        for (SourceInstruction instruction : instructions) {
            int word = encodeInstruction(instruction, labels, instructionCount);
            machineWords.add(word);
        }

        return machineWords;
    }

    private static int encodeInstruction(
            SourceInstruction source,
            Map<String, Integer> labels,
            int instructionCount
    ) throws AssemblyException {

        String text = source.text.trim();
        String[] firstSplit = text.split("\\s+", 2);
        String mnemonic = firstSplit[0].toUpperCase(Locale.ROOT);
        String operandText = firstSplit.length == 2 ? firstSplit[1].trim() : "";

        Integer opcodeObject = OPCODES.get(mnemonic);
        if (opcodeObject == null) {
            throw error(source.lineNumber,
                    "Unknown instruction '" + firstSplit[0] + "'.");
        }
        int opcode = opcodeObject.intValue();

        List<String> operands = splitOperands(operandText, source.lineNumber);

        if ("ADD".equals(mnemonic)
                || "SUB".equals(mnemonic)
                || "AND".equals(mnemonic)
                || "OR".equals(mnemonic)) {

            requireOperandCount(mnemonic, operands, 3, source.lineNumber);
            int rd = parseRegister(operands.get(0), source.lineNumber);
            requireWritableDestination(rd, operands.get(0), source.lineNumber);
            int rs = parseRegister(operands.get(1), source.lineNumber);
            int rt = parseRegister(operands.get(2), source.lineNumber);
            return encodeRType(opcode, rs, rt, rd, 0);
        }

        if ("SLL".equals(mnemonic) || "SRL".equals(mnemonic)) {
            requireOperandCount(mnemonic, operands, 3, source.lineNumber);
            int rd = parseRegister(operands.get(0), source.lineNumber);
            requireWritableDestination(rd, operands.get(0), source.lineNumber);
            int rs = parseRegister(operands.get(1), source.lineNumber);
            int shamt = parseInteger(operands.get(2), source.lineNumber,
                    "shift amount");
            requireUnsignedRange(shamt, 2, source.lineNumber, "Shift amount");
            return encodeRType(opcode, rs, 0, rd, shamt);
        }

        if ("ADDI".equals(mnemonic)) {
            requireOperandCount(mnemonic, operands, 3, source.lineNumber);
            int rt = parseRegister(operands.get(0), source.lineNumber);
            requireWritableDestination(rt, operands.get(0), source.lineNumber);
            int rs = parseRegister(operands.get(1), source.lineNumber);
            int immediate = parseInteger(operands.get(2), source.lineNumber,
                    "immediate");
            int immediateBits = encodeSigned(immediate, 4, source.lineNumber,
                    "ADDI immediate");
            return encodeIType(opcode, rs, rt, immediateBits);
        }

        if ("LW".equals(mnemonic) || "SW".equals(mnemonic)) {
            requireOperandCount(mnemonic, operands, 2, source.lineNumber);
            int rt = parseRegister(operands.get(0), source.lineNumber);
            if ("LW".equals(mnemonic)) {
                requireWritableDestination(rt, operands.get(0), source.lineNumber);
            }
            MemoryReference memory = parseMemoryReference(
                    operands.get(1), source.lineNumber
            );

            requireUnsignedRange(memory.offset, 4, source.lineNumber,
                    mnemonic + " offset");
            return encodeIType(opcode, memory.baseRegister, rt, memory.offset);
        }

        if ("BEQ".equals(mnemonic) || "BNE".equals(mnemonic)) {
            requireOperandCount(mnemonic, operands, 3, source.lineNumber);
            int rs = parseRegister(operands.get(0), source.lineNumber);
            int rt = parseRegister(operands.get(1), source.lineNumber);
            int offset = resolveBranchOffset(
                    operands.get(2), source, labels, instructionCount
            );
            int offsetBits = encodeSigned(offset, 4, source.lineNumber,
                    mnemonic + " branch offset");
            return encodeIType(opcode, rs, rt, offsetBits);
        }

        if ("JUMP".equals(mnemonic)) {

            requireOperandCount(mnemonic, operands, 1, source.lineNumber);

            int address = resolveJumpAddress(
                    operands.get(0),
                    source,
                    labels
            );

            requireUnsignedRange(address, 8, source.lineNumber,
                    "JUMP address");

            return encodeJType(opcode, address);
        }

        if ("IN".equals(mnemonic)) {
            requireOperandCount(mnemonic, operands, 1, source.lineNumber);
            int rd = parseRegister(operands.get(0), source.lineNumber);
            requireWritableDestination(rd, operands.get(0), source.lineNumber);
            return encodeRType(opcode, 0, 0, rd, 0);
        }

        if ("OUT".equals(mnemonic)) {
            requireOperandCount(mnemonic, operands, 1, source.lineNumber);
            int rd = parseRegister(operands.get(0), source.lineNumber);
            return encodeRType(opcode, 0, 0, rd, 0);
        }

        
        throw error(source.lineNumber,
                "Instruction '" + mnemonic + "' is not implemented.");
    }

    private static int encodeRType(int opcode, int rs, int rt, int rd, int shamt) {
        return ((opcode & 0xF) << 8)
                | ((rs & 0x3) << 6)
                | ((rt & 0x3) << 4)
                | ((rd & 0x3) << 2)
                | (shamt & 0x3);
    }

    private static int encodeIType(int opcode, int rs, int rt, int immediate) {
        return ((opcode & 0xF) << 8)
                | ((rs & 0x3) << 6)
                | ((rt & 0x3) << 4)
                | (immediate & 0xF);
    }

    private static int encodeJType(int opcode, int address) {
        return ((opcode & 0xF) << 8) | (address & 0xFF);
    }

    private static MemoryReference parseMemoryReference(
            String operand,
            int lineNumber
    ) throws AssemblyException {

        Matcher matcher = MEMORY_OPERAND.matcher(operand.trim());
        if (!matcher.matches()) {
            throw error(lineNumber,
                    "Invalid memory operand '" + operand
                            + "'. Expected format: offset(baseRegister), for example 3($zero)."
            );
        }

        int offset = parseInteger(matcher.group(1), lineNumber, "memory offset");
        int baseRegister = parseRegister(matcher.group(2), lineNumber);
        return new MemoryReference(offset, baseRegister);
    }

    private static int resolveBranchOffset(
            String target,
            SourceInstruction source,
            Map<String, Integer> labels,
            int instructionCount
    ) throws AssemblyException {

        Integer numeric = tryParseInteger(target);
        int offset;
        int targetAddress;

        if (numeric != null) {
            // A numeric BEQ/BNE operand is already a PC-relative offset.
            offset = numeric.intValue();
            targetAddress = source.address + 1 + offset;
        } else {
            Integer labelAddress = labels.get(normalizeLabel(target));
            if (labelAddress == null) {
                throw error(source.lineNumber,
                        "Undefined branch label '" + target + "'.");
            }

            targetAddress = labelAddress.intValue();
            offset = targetAddress - (source.address + 1);
        }

        // A label is allowed immediately after the final instruction.
        // This makes END: a valid branch target for a program that terminates
        // when the PC advances past the last encoded instruction.
        if (targetAddress < 0 || targetAddress > instructionCount) {
            throw error(source.lineNumber,
                    "Branch target address " + targetAddress
                            + " is outside the program. Valid target addresses are 0 to "
                            + instructionCount + ".");
        }

        return offset;
    }

    private static int resolveJumpAddress(
            String target,
            SourceInstruction source,
            Map<String, Integer> labels
    ) throws AssemblyException {

        Integer numeric = tryParseInteger(target);

        if (numeric != null) {
            return numeric.intValue();
        }

        Integer address = labels.get(normalizeLabel(target));

        if (address == null) {
            throw error(source.lineNumber,
                    "Undefined jump label '" + target + "'.");
        }

        // JUMP uses direct addressing: the 8-bit field stores the absolute
        // instruction address of the target label.
        return address.intValue();
    }

    private static List<String> splitOperands(
            String operandText,
            int lineNumber
    ) throws AssemblyException {

        List<String> operands = new ArrayList<String>();
        if (operandText.isEmpty()) {
            return operands;
        }

        StringBuilder current = new StringBuilder();
        int parenthesisDepth = 0;

        for (int i = 0; i < operandText.length(); i++) {
            char c = operandText.charAt(i);

            if (c == '(') {
                parenthesisDepth++;
                current.append(c);
            } else if (c == ')') {
                parenthesisDepth--;
                if (parenthesisDepth < 0) {
                    throw error(lineNumber,
                            "Unmatched ')' in operand list.");
                }
                current.append(c);
            } else if (c == ',' && parenthesisDepth == 0) {
                addOperand(operands, current, lineNumber);
                current.setLength(0);
            } else {
                current.append(c);
            }
        }

        if (parenthesisDepth != 0) {
            throw error(lineNumber,
                    "Unmatched '(' in operand list.");
        }

        addOperand(operands, current, lineNumber);
        return operands;
    }

    private static void addOperand(
            List<String> operands,
            StringBuilder current,
            int lineNumber
    ) throws AssemblyException {

        String operand = current.toString().trim();
        if (operand.isEmpty()) {
            throw error(lineNumber,
                    "Empty operand. Check commas in the instruction.");
        }
        operands.add(operand);
    }

    private static int parseRegister(String token, int lineNumber)
            throws AssemblyException {

        String normalized = token.trim().toLowerCase(Locale.ROOT);

        if (!normalized.startsWith("$")) {
            throw error(lineNumber,
                    "Register '" + token
                            + "' must start with '$' (for example $s0, $s1, $t0, or $zero).");
        }

        Integer register = REGISTERS.get(normalized);

        if (register == null) {
            throw error(lineNumber,
                    "Invalid register '" + token
                            + "'. Valid registers: $zero/$r0, $s0/$r1, $s1/$r2, $t0/$r3."
            );
        }

        return register.intValue();
    }

    private static void requireWritableDestination(
            int register,
            String token,
            int lineNumber
    ) throws AssemblyException {

        if (register == 0) {
            throw error(lineNumber,
                    "Register '" + token
                            + "' is the zero register and cannot be used as a destination.");
        }
    }

    private static int parseInteger(
            String token,
            int lineNumber,
            String description
    ) throws AssemblyException {

        Integer value = tryParseInteger(token);
        if (value == null) {
            throw error(lineNumber,
                    "Invalid " + description + " '" + token + "'.");
        }
        return value.intValue();
    }

   
    private static Integer tryParseInteger(String token) {
        String text = token.trim();
        if (text.isEmpty()) {
            return null;
        }

        int sign = 1;
        int index = 0;

        if (text.charAt(0) == '+' || text.charAt(0) == '-') {
            if (text.charAt(0) == '-') {
                sign = -1;
            }
            index++;
        }

        if (index >= text.length()) {
            return null;
        }

        int radix = 10;
        if (text.regionMatches(true, index, "0x", 0, 2)) {
            radix = 16;
            index += 2;
        } else if (text.regionMatches(true, index, "0b", 0, 2)) {
            radix = 2;
            index += 2;
        }

        if (index >= text.length()) {
            return null;
        }

        String digits = text.substring(index);
        try {
            long magnitude = Long.parseLong(digits, radix);
            long signedValue = sign * magnitude;
            if (signedValue < Integer.MIN_VALUE || signedValue > Integer.MAX_VALUE) {
                return null;
            }
            return Integer.valueOf((int) signedValue);
        } catch (NumberFormatException e) {
            return null;
        }
    }

    private static int encodeSigned(
            int value,
            int bitCount,
            int lineNumber,
            String description
    ) throws AssemblyException {

        int minimum = -(1 << (bitCount - 1));
        int maximum = (1 << (bitCount - 1)) - 1;

        if (value < minimum || value > maximum) {
            throw error(lineNumber,
                    description + " must be in the range "
                            + minimum + " to " + maximum + ", but found " + value + "."
            );
        }

        return value & ((1 << bitCount) - 1);
    }

    private static void requireUnsignedRange(
            int value,
            int bitCount,
            int lineNumber,
            String description
    ) throws AssemblyException {

        int maximum = (1 << bitCount) - 1;
        if (value < 0 || value > maximum) {
            throw error(lineNumber,
                    description + " must be in the range 0 to "
                            + maximum + ", but found " + value + "."
            );
        }
    }

    private static void requireOperandCount(
            String mnemonic,
            List<String> operands,
            int expected,
            int lineNumber
    ) throws AssemblyException {

        if (operands.size() != expected) {
            throw error(lineNumber,
                    mnemonic + " expects " + expected + " operand(s), but found "
                            + operands.size() + "."
            );
        }
    }

    private static String stripComment(String line) {
        int commentStart = line.length();

        int semicolon = line.indexOf(';');
        if (semicolon >= 0) {
            commentStart = Math.min(commentStart, semicolon);
        }

        int hash = line.indexOf('#');
        if (hash >= 0) {
            commentStart = Math.min(commentStart, hash);
        }

        int doubleSlash = line.indexOf("//");
        if (doubleSlash >= 0) {
            commentStart = Math.min(commentStart, doubleSlash);
        }

        return line.substring(0, commentStart);
    }

    private static String normalizeLabel(String label) {
        return label.trim().toUpperCase(Locale.ROOT);
    }

    private static void writeHexOutput(
            Path outputPath,
            List<Integer> machineWords
    ) throws IOException {

        Path parent = outputPath.toAbsolutePath().getParent();

        if (parent != null) {
            Files.createDirectories(parent);
        }

        BufferedWriter writer = Files.newBufferedWriter(
                outputPath,
                StandardCharsets.UTF_8
        );

        System.out.println("\nMachine Code:");
        System.out.println("-------------");

        for (Integer word : machineWords) {

            int machineCode = word & 0xFFF;

            
            String binary = Integer.toBinaryString(machineCode);

            while (binary.length() < 12) {
                binary = "0" + binary;
            }

          
            String hexadecimal = String.format("%03X", machineCode);
           
            System.out.println(binary);

            writer.write(hexadecimal);
            writer.newLine();
        }

        writer.close();
    }

    private static AssemblyException error(int lineNumber, String message) {
        return new AssemblyException("Line " + lineNumber + ": " + message);
    }

    private static Map<String, Integer> createOpcodeTable() {
        Map<String, Integer> map = new HashMap<String, Integer>();
        map.put("ADD",  0x0);
        map.put("SUB",  0x1);
        map.put("AND",  0x2);
        map.put("OR",   0x3);
        map.put("SLL",  0x4);
        map.put("SRL",  0x5);
        map.put("ADDI", 0x6);
        map.put("LW",   0x7);
        map.put("SW",   0x8);
        map.put("BEQ",  0x9);
        map.put("BNE",  0xA);
        map.put("JUMP", 0xB);
        map.put("IN",   0xC);
        map.put("OUT",  0xD);
        return map;
    }

    private static Map<String, Integer> createRegisterTable() {
        Map<String, Integer> map = new HashMap<String, Integer>();

        map.put("$zero", 0);
        map.put("$r0", 0);

        map.put("$s0", 1);
        map.put("$r1", 1);

        map.put("$s1", 2);
        map.put("$r2", 2);

        map.put("$t0", 3);
        map.put("$r3", 3);

        return map;
    }

    private static final class SourceInstruction {
        private final int address;
        private final int lineNumber;
        private final String text;

        private SourceInstruction(int address, int lineNumber, String text) {
            this.address = address;
            this.lineNumber = lineNumber;
            this.text = text;
        }
    }

    private static final class MemoryReference {
        private final int offset;
        private final int baseRegister;

        private MemoryReference(int offset, int baseRegister) {
            this.offset = offset;
            this.baseRegister = baseRegister;
        }
    }

    public static final class AssemblyException extends Exception {
        private static final long serialVersionUID = 1L;

        private AssemblyException(String message) {
            super(message);
        }
    }
}