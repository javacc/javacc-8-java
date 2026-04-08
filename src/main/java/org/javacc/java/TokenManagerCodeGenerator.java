/*
 * Copyright (c) 2020-2025, Sreeni Viswanadha <sreeni@viswanadha.net>.
 * Copyright (c) 2024-2025, Marc Mazas <mazas.marc@gmail.com>.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *     * Redistributions of source code must retain the above copyright notice,
 *       this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the names of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived from
 *       this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
 */
package org.javacc.java;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.javacc.parser.CodeGeneratorSettings;
import org.javacc.parser.Context;
import org.javacc.parser.JavaCCParserConstants;
import org.javacc.parser.Options;
import org.javacc.parser.Token;
import org.javacc.parser.TokenizerData;
import org.javacc.parser.TokenizerData.MatchType;
import org.javacc.utils.CodeBuilder;

/** Class that implements a table driven code generator for the token manager in Java. */
class TokenManagerCodeGenerator implements org.javacc.parser.TokenManagerCodeGenerator {

    private static final String tokenManagerTemplate = "/templates/java/TokenManagerDriver.template";

    private final Context context;
    private JavaCodeBuilder jcb;
    private static final String EOL = System.getProperty("line.separator");

    TokenManagerCodeGenerator(final Context context) {
        this.context = context;
    }

    @Override
    public void generateCode(final CodeGeneratorSettings settings, final TokenizerData tokenizerData) {
        settings.putAll(Options.getOptions());

        settings.put("maxOrdinal", tokenizerData.allMatches.size());
        settings.put("maxLexStates", tokenizerData.lexStateNames.length);
        settings.put("nfaSize", tokenizerData.nfa.size());
        settings.put("charsVectorSize", ((Character.MAX_VALUE >> 6) + 1));
        settings.put("stateSetSize", tokenizerData.nfa.size());
        settings.put("parserName", tokenizerData.parserName);
        settings.put("maxLongs", (tokenizerData.allMatches.size() / 64) + 1);
        settings.put("parserName", tokenizerData.parserName);
        settings.put("charStreamName", Options.getCharStreamName());
        settings.put("defaultLexState", tokenizerData.lexStateNames[tokenizerData.defaultLexState]);
        settings.put("decls", tokenizerData.decls);
        settings.put("generatedStates", tokenizerData.nfa.size());
        settings.put("initMatch", tokenizerData.initialMatchForLexState);

        final String tmSuperClass = (String) settings.get(Options.UO__TOKEN_MANAGER_SUPER_CLASS);
        settings.put(
            "tmSuperClass",
            ((tmSuperClass == null) || tmSuperClass.equals("")) ? "" : "extends " + tmSuperClass
        );
        settings.put("noDfa", Options.getNoDfa());

        try {
            final File file = new File(Options.getOutputDirectory(), tokenizerData.parserName + "TokenManager.java");
            jcb = JavaCodeBuilder.of(context, settings).setFile(file);
            jcb.setPackageName(JavaUtil.parsePackage(context));

            if (context.globals().cu_to_insertion_point_1.size() != 0) {
                List<String> tokens = null;
                final Object firstToken = context.globals().cu_to_insertion_point_1.get(0);
                jcb.printTokenSetup((Token) firstToken);
                for (final Token t : context.globals().cu_to_insertion_point_1) {
                    if (t.kind == JavaCCParserConstants.IMPORT) {
                        tokens = new ArrayList<>();
                    } else if ((tokens != null) && (t.kind == JavaCCParserConstants.SEMICOLON)) {
                        jcb.println("import", String.join("", tokens), ";");
                        tokens = null;
                    } else if (tokens != null) {
                        tokens.add(CodeBuilder.toString(t));
                    }
                }
                jcb.println();
            }

            jcb.println("/* Beginning of code from " + tokenManagerTemplate + " */");
            jcb.println();
            jcb.printTemplate(tokenManagerTemplate);
            jcb.println();
            jcb.println("/* End of code from " + tokenManagerTemplate + " */");
            jcb.println();

            jcb.println("  /* Match info. */");
            jcb.println();
            dumpMatchInfo(jcb, tokenizerData);

            if (!Options.getNoDfa()) {
                jcb.println("  /* DFA tables. */");
                jcb.println();
                dumpDfaTables(jcb, tokenizerData);
            }

            jcb.println("  /* NFA tables. */");
            jcb.println();
            dumpNfaTables(jcb, tokenizerData);

            jcb.println("  static {");
            if (!Options.getNoDfa()) {
                jcb.println("    InitStartAndSize();");
            }
            jcb.println("    initJjChars();");
            jcb.println("  }");
            jcb.println();
            jcb.println("}");
        } catch (final IOException ioe) {
            ioe.printStackTrace();
            assert (false);
        }
    }

    @Override
    public void finish(final CodeGeneratorSettings settings, final TokenizerData tokenizerData) {
        if (!Options.getBuildTokenManager()) {
            return;
        }

        try {
            jcb.close();
        } catch (final IOException ioe) {
            ioe.printStackTrace();
        }
    }

    private static void dumpDfaTables(final JavaCodeBuilder jcb, final TokenizerData tokenizerData) {
        /* stringLiterals — collect into int[], emit via init method to avoid <clinit> overflow. */
        final List<Integer> slData = new ArrayList<>();
        final Map<Integer, int[]> startAndSize = new HashMap<>();
        for (final int key : tokenizerData.literalSequence.keySet()) {
            final int[] arr = new int[2];
            final List<String> l = tokenizerData.literalSequence.get(key);
            final List<Integer> kinds = tokenizerData.literalKinds.get(key);
            arr[0] = slData.size();
            arr[1] = l.size();
            int j = 0;
            for (final String s : l) {
                final int kind = kinds.get(j);
                final boolean ignoreCase = tokenizerData.ignoreCaseKinds.contains(kind);
                slData.add(s.length());
                slData.add(ignoreCase ? 1 : 0);
                for (int k = 0; k < s.length(); k++) {
                    slData.add((int) s.charAt(k));
                }
                if (ignoreCase) {
                    for (int k = 0; k < s.length(); k++) {
                        slData.add((int) s.toUpperCase().charAt(k));
                    }
                }
                slData.add(kind);
                slData.add(tokenizerData.kindToNfaStartState.get(kind));
                j++;
            }
            startAndSize.put(key, arr);
        }
        final int[] stringLiteralsArr = new int[slData.size()];
        for (int idx = 0; idx < slData.size(); idx++) {
            stringLiteralsArr[idx] = slData.get(idx);
        }
        JavaArrayHelper.emitIntArray(jcb, "  ", "private", "stringLiterals", stringLiteralsArr);

        /* startAndSize. */
        jcb.println("  private static final java.util.Map<Integer, int[]> startAndSize =");
        jcb.println("      new java.util.HashMap<Integer, int[]>();");
        jcb.println();

        /* InitStartAndSize. */
        jcb.println("  // format of \"startAndSize.put(k, new int[] {ix, sz})\":");
        jcb.println(
            "  // k: key of map of lists of literals starting by char 'c', indexed by ((LexicalState << 16 | (int) c)"
        );
        jcb.println("  // ix: index (list's start in stringLiterals)");
        jcb.println("  // sz: list's size");
        jcb.println("  private static void InitStartAndSize() {");
        for (final int key : tokenizerData.literalSequence.keySet()) {
            final int[] arr = startAndSize.get(key);
            jcb.println("    startAndSize.put(" + key + ", new int[] {" + arr[0] + ", " + arr[1] + "});");
        }
        jcb.println("  }");
        jcb.println();
    }

    private static void dumpNfaTables(final JavaCodeBuilder jcb, final TokenizerData tokenizerData) {
        /* canMatchAnyChar. */
        jcb.print("  private static final int[] canMatchAnyChar = {");
        int v = 0;
        for (int i = 0; i < tokenizerData.wildcardKind.size(); i++) {
            if (v++ > 0) {
                jcb.print(", ");
            } else {
                jcb.println();
                jcb.print("    ");
            }
            jcb.print(tokenizerData.wildcardKind.get(i));
        }
        if (!tokenizerData.wildcardKind.isEmpty()) {
            jcb.println();
            jcb.println("  };");
        } else {
            jcb.println("};");
        }
        jcb.println();

        /* jjInitStates. */
        jcb.print("  private static final int[] jjInitStates = {");
        v = 0;
        for (final int i : tokenizerData.initialStates.keySet()) {
            if (v++ > 0) {
                jcb.print(", ");
            } else {
                jcb.println();
                jcb.print("    ");
            }
            jcb.print(tokenizerData.initialStates.get(i));
        }
        if (!tokenizerData.initialStates.isEmpty()) {
            jcb.println();
            jcb.println("  };");
        } else {
            jcb.println("};");
        }
        jcb.println();

        /* jjInitialMatchForLexState. */
        jcb.print("  private static final int[] jjInitialMatchForLexState = {");
        v = 0;
        for (int i = 0; i < tokenizerData.lexStateNames.length; i++) {
            if (v++ > 0) {
                jcb.print(", ");
            } else {
                jcb.println();
                jcb.print("    ");
            }
            jcb.print(tokenizerData.initialMatchForLexState[i]);
        }
        jcb.println("};");
        jcb.println();

        // We do the following for Java so that the generated code is reasonable
        // size and can be compiled. May not be needed for other languages.

        /* EMPTY_CHAR_DATA. */
        jcb.println("  private static final long[] EMPTY_CHAR_DATA = new long[] {};");
        jcb.println();

        /* CharDataConsts. */
        jcb.println("  private static final class CharDataConsts {");
        jcb.println();

        /* jjCharData into a buffer. */
        final Map<Integer, TokenizerData.NfaState> nfa = tokenizerData.nfa;
        final Map<String, String> charDataVars = new HashMap<String, String>();
        final Map<String, String> charDataCdbs = new HashMap<String, String>();

        final StringBuilder sb = new StringBuilder(64 + 18 * nfa.size());
        sb.append("    private static final long[][] jjCharData = {");
        final String charDataVarPrefix = "CHAR_DATA";
        final StringBuilder charDataBuilder = new StringBuilder(64);
        for (int i = 0; i < nfa.size(); i++) {
            if (i > 0) {
                sb.append(',').append(EOL);
            } else {
                sb.append(EOL);
            }
            charDataBuilder.setLength(0);
            // We have a lot of similar states. So factor them so we don't get "Code too large" errors.
            final TokenizerData.NfaState tmp = nfa.get(i);
            if (tmp == null) {
                //        sb.append("      EMPTY_CHAR_DATA").append(EOL);
                sb.append("      /* ").append(i).append(" */ EMPTY_CHAR_DATA").append(EOL);
            } else {
                charDataBuilder.append("new long[] {");
                final BitSet bits = new BitSet();
                for (final char c : tmp.characters) {
                    bits.set(c);
                }
                final long[] longs = bits.toLongArray();
                for (int k = 0; k < longs.length; k++) {
                    int rep = 1;
                    while (((k + rep) < longs.length) && (longs[k + rep] == longs[k])) {
                        rep++;
                    }
                    if (k > 0) {
                        charDataBuilder.append(", ");
                    }
                    charDataBuilder.append(rep).append(", ");
                    charDataBuilder.append(Long.toString(longs[k])).append("L");
                    k += rep - 1;
                }
                charDataBuilder.append("}");
                final String cdb = charDataBuilder.toString();
                String var = charDataVars.get(cdb);
                if (var == null) {
                    var = charDataVarPrefix + (charDataVars.size() + 1);
                    charDataVars.put(cdb, var);
                    charDataCdbs.put(var, cdb);
                }
                //        sb.append("      " + var);
                sb.append("      /* ").append(i).append(" */ ").append(var);
            }
        }
        if (!nfa.isEmpty()) {
            sb.append(EOL).append("    };").append(EOL);
        } else {
            sb.append("  };").append(EOL);
        }

        // in order, for easier comparison with C# & C++
        for (int k = 1; k <= charDataCdbs.size(); k++) {
            final String key = charDataVarPrefix + Integer.toString(k);
            jcb.println("    private static final long[] " + key + " = " + charDataCdbs.get(key) + ";");
        }
        jcb.println();

        // now print jjCharData buffer
        jcb.println(sb);

        /* end class CharDataConsts. */
        jcb.println("  }");
        jcb.println();

        /* jjcompositeState and jjnextStateSet are now flattened; EMPTY_STATE_SET no longer needed. */

        /* jjcompositeState — flatten int[][] to 1D for clinit safety and cache efficiency. */
        final List<int[]> compositeRows = new ArrayList<>(nfa.size());
        for (int i = 0; i < nfa.size(); i++) {
            final TokenizerData.NfaState tmp = nfa.get(i);
            if (tmp == null || tmp.compositeStates.isEmpty()) {
                compositeRows.add(null);
            } else {
                final int[] row = new int[tmp.compositeStates.size()];
                int k = 0;
                for (final int st : tmp.compositeStates) {
                    row[k++] = st;
                }
                compositeRows.add(row);
            }
        }
        final JavaArrayHelper.FlatIntArray2D flatComposite = JavaArrayHelper.flatten(compositeRows);
        JavaArrayHelper.emitFlatIntArray2D(jcb, "  ", "private", "jjcompositeState", flatComposite);

        /* jjmatchKinds — emit via init method. */
        final int[] matchKindsArr = new int[nfa.size()];
        for (int i = 0; i < nfa.size(); i++) {
            final TokenizerData.NfaState tmp = nfa.get(i);
            matchKindsArr[i] = (tmp == null) ? Integer.MAX_VALUE : tmp.kind;
        }
        JavaArrayHelper.emitIntArray(jcb, "  ", "private", "jjmatchKinds", matchKindsArr);

        /* jjnextStateSet — flatten int[][] to 1D for clinit safety and cache efficiency. */
        final List<int[]> nextStateRows = new ArrayList<>(nfa.size());
        for (int i = 0; i < nfa.size(); i++) {
            final TokenizerData.NfaState tmp = nfa.get(i);
            if (tmp == null || tmp.nextStates.isEmpty()) {
                nextStateRows.add(null);
            } else {
                final int[] row = new int[tmp.nextStates.size()];
                int k = 0;
                for (final int s : tmp.nextStates) {
                    row[k++] = s;
                }
                nextStateRows.add(row);
            }
        }
        final JavaArrayHelper.FlatIntArray2D flatNextState = JavaArrayHelper.flatten(nextStateRows);
        JavaArrayHelper.emitFlatIntArray2D(jcb, "  ", "private", "jjnextStateSet", flatNextState);
    }

    private static void dumpMatchInfo(final JavaCodeBuilder jcb, final TokenizerData tokenizerData) {
        final Map<Integer, TokenizerData.MatchInfo> allMatches = tokenizerData.allMatches;

        // A bit ugly.

        final BitSet toSkip = new BitSet(allMatches.size());
        final BitSet toSpecial = new BitSet(allMatches.size());
        final BitSet toMore = new BitSet(allMatches.size());
        final BitSet toToken = new BitSet(allMatches.size());
        final int[] newStates = new int[allMatches.size()];
        toSkip.set(allMatches.size() + 1, true);
        toToken.set(allMatches.size() + 1, true);
        toMore.set(allMatches.size() + 1, true);
        toSpecial.set(allMatches.size() + 1, true);

        /* jjstrLiteralImages — collect into String[], emit via init method. */
        final String[] literalImages = new String[allMatches.size()];
        for (int i = 0; i < allMatches.size(); i++) {
            final TokenizerData.MatchInfo matchInfo = allMatches.get(i);
            switch (matchInfo.matchType) {
                case SKIP:
                    toSkip.set(i);
                    break;
                case SPECIAL_TOKEN:
                    toSpecial.set(i);
                    break;
                case MORE:
                    toMore.set(i);
                    break;
                case TOKEN:
                    toToken.set(i);
                    break;
            }
            newStates[i] = matchInfo.newLexState;
            final String image = matchInfo.image;
            if (image != null) {
                final StringBuilder imgBuilder = new StringBuilder("\"");
                for (int j = 0; j < image.length(); j++) {
                    final int cj = image.charAt(j);
                    switch (cj) {
                        case '\b':
                            imgBuilder.append("\\b");
                            continue;
                        case '\t':
                            imgBuilder.append("\\t");
                            continue;
                        case '\n':
                            imgBuilder.append("\\n");
                            continue;
                        case '\f':
                            imgBuilder.append("\\f");
                            continue;
                        case '\r':
                            imgBuilder.append("\\r");
                            continue;
                        case '\"':
                            imgBuilder.append("\\\"");
                            continue;
                        case '\'':
                            imgBuilder.append("\\\'");
                            continue;
                        case '\\':
                            imgBuilder.append("\\\\");
                            continue;
                        default:
                            if (cj <= 0xff) {
                                if (cj < 0x20 || (cj > 0x7e)) {
                                    imgBuilder.append("0x").append(Integer.toHexString(cj));
                                } else {
                                    imgBuilder.append(image.charAt(j));
                                }
                            } else {
                                String hexVal = Integer.toHexString(image.charAt(j));
                                if (hexVal.length() == 3) {
                                    hexVal = "0" + hexVal;
                                }
                                imgBuilder.append("\\u").append(hexVal);
                            }
                            continue;
                    }
                }
                imgBuilder.append("\"");
                literalImages[i] = imgBuilder.toString();
            }
            // null entries stay null in the array
        }
        JavaArrayHelper.emitStringArray(jcb, "  ", "public", "jjstrLiteralImages", literalImages);

        /* Bit masks. */
        generateBitVector(jcb, "jjtoToken", toToken);
        jcb.println();
        generateBitVector(jcb, "jjtoSkip", toSkip);
        jcb.println();
        generateBitVector(jcb, "jjtoSpecial", toSpecial);
        jcb.println();
        generateBitVector(jcb, "jjtoMore", toMore);
        jcb.println();

        /* jjnewLexState — emit via init method. */
        JavaArrayHelper.emitIntArray(jcb, "  ", "private", "jjnewLexState", newStates);

        // Action functions.

        final String staticString = Options.getStatic() ? "  static " : "  ";

        // Token actions.
        jcb.println(staticString + "void TokenLexicalActions(Token matchedToken) {");
        jcb.println("  // TOKEN lexical actions");
        //    dumpLexicalActions(jcb, allMatches, TokenizerData.MatchType.TOKEN, "matchedToken.kind");
        dumpLexicalActions(jcb, allMatches, TokenizerData.MatchType.TOKEN, "jjmatchedKind");
        jcb.println("  }");
        jcb.println();

        // Skip actions.
        // TODO(sreeni) : Streamline this mess.
        jcb.println(staticString + "void SkipLexicalActions(Token matchedToken) {");
        jcb.println("  // SKIP lexical actions");
        dumpLexicalActions(jcb, allMatches, TokenizerData.MatchType.SKIP, "jjmatchedKind");
        //    jcb.println("  // SPECIAL_TOKEN lexical actions");
        //    dumpLexicalActions(jcb, allMatches, TokenizerData.MatchType.SPECIAL_TOKEN,
        // "jjmatchedKind");
        jcb.println("  }");
        jcb.println();

        // More actions.
        jcb.println(staticString + "void MoreLexicalActions() {");
        //    jcb.println("    jjimageLen += (lengthOfMatch = jjmatchedPos + 1);");
        jcb.println("  // MORE lexical actions");
        dumpLexicalActions(jcb, allMatches, TokenizerData.MatchType.MORE, "jjmatchedKind");
        jcb.println("  }");
        jcb.println();
    }

    private static void dumpLexicalActions(
        final JavaCodeBuilder jcb,
        final Map<Integer, TokenizerData.MatchInfo> allMatches,
        final TokenizerData.MatchType matchType,
        final String kindString
    ) {
        jcb.println("    switch (" + kindString + ") {");
        for (final int i : allMatches.keySet()) {
            final TokenizerData.MatchInfo matchInfo = allMatches.get(i);
            if ((matchInfo.action == null) || (matchInfo.matchType != matchType)) {
                continue;
            }
            jcb.println("      case " + i + ": {");
            // TODO check (MMa start added) comes from v7 output cf. JSqlParser
            if (matchInfo.matchType == MatchType.SKIP) {
            } else if (matchInfo.matchType == MatchType.MORE) {
                jcb.println("        jjimageLen += (lengthOfMatch = jjmatchedPos);");
            } else if (matchInfo.matchType == MatchType.TOKEN) {
                jcb.println(
                    "        image.append(input_stream.GetSuffix(jjimageLen + (lengthOfMatch = jjmatchedPos)));"
                );
            }
            // TODO check (MMa end added)
            jcb.println("        " + matchInfo.action.trim());
            jcb.println("        break;");
            jcb.println("      }");
        }
        jcb.println("      default: break;");
        jcb.println("    }");
    }

    private static void generateBitVector(final JavaCodeBuilder jcb, final String name, final BitSet bits) {
        jcb.println();
        jcb.println("  private static final long[] " + name + " = {");
        final long[] longs = bits.toLongArray();
        for (int i = 0; i < longs.length; i++) {
            if (i > 0) {
                jcb.print(",");
            }
            // codeGenerator.genCode("0x" + Long.toHexString(longs[i]) + "L");
            jcb.print("    " + Long.toString(longs[i]) + "L");
        }
        jcb.println();
        jcb.println("  };");
    }
}
