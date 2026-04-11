/*
 * Copyright (c) 2025, JavaCC contributors.
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

import java.util.List;

/**
 * Utility for emitting large Java static array declarations that would otherwise
 * exceed the JVM's 64 KB bytecode limit on the {@code <clinit>} method.
 *
 * <p>Instead of generating inline array initializers that all compile into
 * {@code <clinit>}, this helper generates dedicated {@code _init()} methods.
 * For very large arrays the init body is further split across multiple chunk
 * methods so that no single method exceeds the bytecode limit.
 *
 * <p>For 2D arrays ({@code int[][]}), this helper can flatten them into a
 * contiguous 1D representation with offset/length arrays, eliminating both
 * the {@code <clinit>} problem and the per-row object header overhead.
 */
final class JavaArrayHelper {

  /**
   * Maximum number of elements emitted per init chunk method.
   * Each {@code r[i]=val;} compiles to roughly 8 bytes of bytecode, so 4000
   * elements is about 32 KB, well within the 64 KB limit.
   */
  private static final int CHUNK_SIZE = 4000;

  /** Elements per line in the generated source for readability. */
  private static final int ELEMENTS_PER_LINE = 16;

  private JavaArrayHelper() {}

  // ----------------------------------------------------------------
  // int[]
  // ----------------------------------------------------------------

  /**
   * Emits a {@code static final int[]} field backed by init method(s).
   *
   * @param jcb    the code builder
   * @param indent leading whitespace (e.g. {@code "  "} for a class member)
   * @param vis    visibility keyword ({@code "private"}, {@code "public"}, etc.)
   * @param name   field name
   * @param data   the array data
   */
  static void emitIntArray(
      final JavaCodeBuilder jcb, final String indent,
      final String vis, final String name, final int[] data) {

    jcb.println(indent + vis + " static final int[] " + name + " = " + name + "_init();");
    jcb.println();

    if (data.length <= CHUNK_SIZE) {
      jcb.println(indent + "private static int[] " + name + "_init() {");
      jcb.print(indent + "  return new int[] {");
      appendIntElements(jcb, indent + "    ", data, 0, data.length);
      jcb.println(indent + "  };");
      jcb.println(indent + "}");
    } else {
      final int chunks = (data.length + CHUNK_SIZE - 1) / CHUNK_SIZE;
      jcb.println(indent + "private static int[] " + name + "_init() {");
      jcb.println(indent + "  final int[] r = new int[" + data.length + "];");
      for (int c = 0; c < chunks; c++) {
        jcb.println(indent + "  " + name + "_init_" + c + "(r);");
      }
      jcb.println(indent + "  return r;");
      jcb.println(indent + "}");
      jcb.println();
      for (int c = 0; c < chunks; c++) {
        final int start = c * CHUNK_SIZE;
        final int end = Math.min(start + CHUNK_SIZE, data.length);
        jcb.println(indent + "private static void " + name + "_init_" + c + "(final int[] r) {");
        for (int i = start; i < end; i++) {
          if ((i - start) % ELEMENTS_PER_LINE == 0) {
            if (i > start) {
              jcb.println();
            }
            jcb.print(indent + "  ");
          }
          jcb.print("r[" + i + "]=" + data[i] + "; ");
        }
        jcb.println();
        jcb.println(indent + "}");
        if (c < chunks - 1) {
          jcb.println();
        }
      }
    }
    jcb.println();
  }

  // ----------------------------------------------------------------
  // long[]
  // ----------------------------------------------------------------

  /**
   * Emits a {@code static final long[]} field backed by init method(s).
   *
   * <p>Each {@code long} literal compiles to ~12 bytes of bytecode
   * ({@code ldc2_w} + {@code lastore}), so the chunk size is halved
   * compared to {@code int[]} to stay within the 64 KB limit.</p>
   *
   * @param jcb    the code builder
   * @param indent leading whitespace
   * @param vis    visibility keyword
   * @param name   field name
   * @param data   the array data
   */
  static void emitLongArray(
      final JavaCodeBuilder jcb, final String indent,
      final String vis, final String name, final long[] data) {

    // long literals are larger in bytecode, so use a smaller chunk
    final int longChunkSize = CHUNK_SIZE / 2;

    jcb.println(indent + vis + " static final long[] " + name + " = " + name + "_init();");
    jcb.println();

    if (data.length <= longChunkSize) {
      jcb.println(indent + "private static long[] " + name + "_init() {");
      jcb.print(indent + "  return new long[] {");
      jcb.println();
      for (int i = 0; i < data.length; i++) {
        if (i % 8 == 0) {
          if (i > 0) {
            jcb.println();
          }
          jcb.print(indent + "    ");
        }
        jcb.print(data[i] + "L");
        if (i < data.length - 1) {
          jcb.print(", ");
        }
      }
      jcb.println();
      jcb.println(indent + "  };");
      jcb.println(indent + "}");
    } else {
      final int chunks = (data.length + longChunkSize - 1) / longChunkSize;
      jcb.println(indent + "private static long[] " + name + "_init() {");
      jcb.println(indent + "  final long[] r = new long[" + data.length + "];");
      for (int c = 0; c < chunks; c++) {
        jcb.println(indent + "  " + name + "_init_" + c + "(r);");
      }
      jcb.println(indent + "  return r;");
      jcb.println(indent + "}");
      jcb.println();
      for (int c = 0; c < chunks; c++) {
        final int start = c * longChunkSize;
        final int end = Math.min(start + longChunkSize, data.length);
        jcb.println(indent + "private static void " + name + "_init_" + c + "(final long[] r) {");
        for (int i = start; i < end; i++) {
          if ((i - start) % 8 == 0) {
            if (i > start) {
              jcb.println();
            }
            jcb.print(indent + "  ");
          }
          jcb.print("r[" + i + "]=" + data[i] + "L; ");
        }
        jcb.println();
        jcb.println(indent + "}");
        if (c < chunks - 1) {
          jcb.println();
        }
      }
    }
    jcb.println();
  }

  // ----------------------------------------------------------------
  // String[]
  // ----------------------------------------------------------------

  /**
   * Emits a {@code static final String[]} field backed by init method(s).
   *
   * @param data array of already-quoted string values (e.g. {@code "\"hello\""});
   *             {@code null} entries are emitted as the Java literal {@code null}
   */
  static void emitStringArray(
      final JavaCodeBuilder jcb, final String indent,
      final String vis, final String name, final String[] data) {

    jcb.println(indent + vis + " static final String[] " + name + " = " + name + "_init();");
    jcb.println();

    if (data.length <= CHUNK_SIZE) {
      jcb.println(indent + "private static String[] " + name + "_init() {");
      jcb.println(indent + "  return new String[] {");
      for (int i = 0; i < data.length; i++) {
        jcb.print(indent + "    " + (data[i] == null ? "null" : data[i]));
        if (i < data.length - 1) {
          jcb.println(",");
        } else {
          jcb.println();
        }
      }
      jcb.println(indent + "  };");
      jcb.println(indent + "}");
    } else {
      final int chunks = (data.length + CHUNK_SIZE - 1) / CHUNK_SIZE;
      jcb.println(indent + "private static String[] " + name + "_init() {");
      jcb.println(indent + "  final String[] r = new String[" + data.length + "];");
      for (int c = 0; c < chunks; c++) {
        jcb.println(indent + "  " + name + "_init_" + c + "(r);");
      }
      jcb.println(indent + "  return r;");
      jcb.println(indent + "}");
      jcb.println();
      for (int c = 0; c < chunks; c++) {
        final int start = c * CHUNK_SIZE;
        final int end = Math.min(start + CHUNK_SIZE, data.length);
        jcb.println(indent + "private static void " + name + "_init_" + c + "(final String[] r) {");
        for (int i = start; i < end; i++) {
          jcb.println(indent + "  r[" + i + "] = " +
              (data[i] == null ? "null" : data[i]) + ";");
        }
        jcb.println(indent + "}");
        if (c < chunks - 1) {
          jcb.println();
        }
      }
    }
    jcb.println();
  }

  // ----------------------------------------------------------------
  // int[][] → flattened 1D representation
  // ----------------------------------------------------------------

  /**
   * Result of flattening a 2D {@code int[][]} array into a contiguous 1D representation.
   */
  static final class FlatIntArray2D {

    final int[] data;
    final int[] offsets;
    final int[] lengths;
    final int rows;

    FlatIntArray2D(final int[] data, final int[] offsets, final int[] lengths, final int rows) {
      this.data = data;
      this.offsets = offsets;
      this.lengths = lengths;
      this.rows = rows;
    }
  }

  /**
   * Flattens a list of {@code int[]} rows into a contiguous representation.
   * Null or empty rows get {@code length == 0} and a valid offset.
   *
   * @param rows list of rows; null entries are treated as empty
   * @return the flat representation
   */
  static FlatIntArray2D flatten(final List<int[]> rows) {
    int totalSize = 0;
    for (final int[] row : rows) {
      if (row != null) {
        totalSize += row.length;
      }
    }
    // Ensure at least 1 element so data array is never zero-length
    final int[] data = new int[Math.max(totalSize, 1)];
    final int[] offsets = new int[rows.size()];
    final int[] lengths = new int[rows.size()];
    int pos = 0;
    for (int i = 0; i < rows.size(); i++) {
      offsets[i] = pos;
      final int[] row = rows.get(i);
      if (row != null && row.length > 0) {
        lengths[i] = row.length;
        System.arraycopy(row, 0, data, pos, row.length);
        pos += row.length;
      }
    }
    return new FlatIntArray2D(data, offsets, lengths, rows.size());
  }

  /**
   * Emits a flattened 2D array as three 1D arrays ({@code _data}, {@code _offsets},
   * {@code _lengths}) plus accessor methods.
   *
   * <p>Generated accessors:
   * <ul>
   *   <li>{@code int NAME(int row, int col)} — element access</li>
   *   <li>{@code int NAME_length(int row)} — row length</li>
   *   <li>{@code int[] NAME_row(int row)} — copy of row (for for-each loops)</li>
   * </ul>
   *
   * @param jcb    the code builder
   * @param indent leading whitespace
   * @param vis    visibility for the underlying arrays
   * @param name   base name (e.g. {@code "jjnextStateSet"})
   * @param flat   the flattened data from {@link #flatten}
   */
  static void emitFlatIntArray2D(
      final JavaCodeBuilder jcb, final String indent,
      final String vis, final String name, final FlatIntArray2D flat) {

    emitIntArray(jcb, indent, vis, name + "_data", flat.data);
    emitIntArray(jcb, indent, vis, name + "_offsets", flat.offsets);
    emitIntArray(jcb, indent, vis, name + "_lengths", flat.lengths);

    // Accessor: element by row+col
    jcb.println(indent + "private static int " + name + "(final int row, final int col) {");
    jcb.println(indent + "  return " + name + "_data[" + name + "_offsets[row] + col];");
    jcb.println(indent + "}");
    jcb.println();

    // Accessor: row length
    jcb.println(indent + "private static int " + name + "_length(final int row) {");
    jcb.println(indent + "  return " + name + "_lengths[row];");
    jcb.println(indent + "}");
    jcb.println();

    // Accessor: get row as array (for for-each compatibility in template)
    jcb.println(indent + "private static int[] " + name + "_row(final int row) {");
    jcb.println(indent + "  final int off = " + name + "_offsets[row];");
    jcb.println(indent + "  final int len = " + name + "_lengths[row];");
    jcb.println(indent + "  final int[] r = new int[len];");
    jcb.println(indent + "  System.arraycopy(" + name + "_data, off, r, 0, len);");
    jcb.println(indent + "  return r;");
    jcb.println(indent + "}");
    jcb.println();
  }

  // ----------------------------------------------------------------
  // Private helpers
  // ----------------------------------------------------------------

  private static void appendIntElements(
      final JavaCodeBuilder jcb, final String indent,
      final int[] data, final int from, final int to) {
    jcb.println();
    for (int i = from; i < to; i++) {
      if ((i - from) % ELEMENTS_PER_LINE == 0) {
        if (i > from) {
          jcb.println();
        }
        jcb.print(indent);
      }
      jcb.print(data[i]);
      if (i < to - 1) {
        jcb.print(", ");
      }
    }
    jcb.println();
  }
}
