// Copyright 2015 The Go Authors.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build linux

package net

import (
	"bytes"
	"io"
	"io/ioutil"
	"sync"
	"testing"
)

type onlyReader struct{ io.Reader }

func sendNext2(l Listener, splice bool) error {
	defer l.Close()
	src, err := l.Accept()
	if err != nil {
		return err
	}

	dst, err := l.Accept()
	if err != nil {
		return err
	}

	var r io.Reader
	if splice {
		r = src
	} else {
		r = onlyReader{src}
	}

	_, err = dst.(*TCPConn).ReadFrom(r)
	src.Close()
	dst.Close()
	return err
}

// returns (src, dst, dial error, listen/splice error chan)
// on success, everything written to 'src' can be read from 'dst'
func setupProxy(net, addr string, splice bool) (Conn, Conn, error, chan error) {
	l, err := Listen(net, addr)
	if err != nil {
		return nil, nil, err, nil
	}
	errc := make(chan error, 1)
	go func() {
		errc <- sendNext2(l, splice)
	}()
	c1, err := Dial(net, addr)
	if err != nil {
		return nil, nil, err, errc
	}
	c2, err := Dial(net, addr)
	if err != nil {
		c1.Close()
		return nil, nil, err, errc
	}
	return c1, c2, nil, errc
}

func TestSimpleSplice(t *testing.T) {
	c1, c2, err, errc := setupProxy("tcp", ":7000", true)
	if err != nil {
		t.Fatal("setup error:", err)
	}

	select {
	case err = <-errc:
		t.Fatal("setup error:", err)
	default:
	}

	// now everthing going into c1 should come out of c2
	var n int
	msg := []byte("TCP SPLICE TEST! WHEEEEEEEE")
	n, err = c1.Write(msg)
	if err != nil {
		t.Error("from src.Write:", err)
	}
	if n != len(msg) {
		t.Errorf("src.Write: short write; wrote %d bytes, but expected %d", n, len(msg))
	}
	out := make([]byte, len(msg))
	_, err = c2.Read(out)
	if err != nil {
		t.Error("from dst.Read:", err)
	} else {
		if !bytes.Equal(msg, out) {
			t.Errorf("TCP splice test: put %s in; got %s out", msg, out)
		}
	}
	c1.Close()
	c2.Close()
	err = <-errc
	if err != nil {
		t.Error("from splice:", err)
	}
}

func TestSpliceMultipart(t *testing.T) {
	c1, c2, err, errc := setupProxy("tcp", ":7001", true)
	if err != nil {
		t.Fatal("setup error:", err)
	}
	select {
	case err = <-errc:
		t.Fatal("setup error:", err)
	default:
	}
	part1 := []byte("this is the first part of the message!")
	part2 := []byte("this is the second part of the message!")

	var n int
	n, err = c1.Write(part1)
	if err != nil {
		t.Error("src.Write:", err)
	}
	if n != len(part1) {
		t.Errorf("c1.Write: short write; wrote %d bytes but expected %d", n, len(part1))
	}
	n, err = c1.Write(part2)
	if err != nil {
		t.Error("src.Write:", err)
	}
	if n != len(part2) {
		t.Errorf("c2.Write: short write; wrote %d bytes but expected %d", n, len(part2))
	}
	out := make([]byte, len(part1)+len(part2))
	_, err = io.ReadFull(c2, out)
	if err != nil {
		t.Error("src.Read:", err)
	}
	expected := append(part1, part2...)
	if !bytes.Equal(out, expected) {
		t.Errorf("put %q and %q in, but got %q out", part1, part2, out)
	}
	c1.Close()
	c2.Close()
	err = <-errc
	if err != nil {
		t.Error("tear-down:", err)
	}
}

func benchmarkTCPLoopback(chunkSize int64, b *testing.B, splice bool) {
	c1, c2, err, errc := setupProxy("tcp", ":7002", splice)
	if err != nil {
		b.Fatal("setup:", err)
	}
	select {
	case err = <-errc:
		b.Fatal("setup:", err)
	default:
	}

	var m sync.Mutex
	m.Lock()
	go func(c Conn, m *sync.Mutex) {
		_, err := io.Copy(ioutil.Discard, c)
		if err != nil {
			b.Fatal("discard:", err)
		}
		m.Unlock()
		c.Close()
	}(c2, &m)

	data := make([]byte, chunkSize)
	b.SetBytes(chunkSize)
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := c1.Write(data)
		if err != nil {
			b.Fatal("write:", err)
		}
	}
	c1.Close()
	m.Lock()
	b.StopTimer()
	err = <-errc
	if err != nil {
		b.Fatal("teardown:", err)
	}
}

func BenchmarkSplice1KBchunk(b *testing.B) {
	benchmarkTCPLoopback(1024, b, true)
}

func BenchmarkSplice4KBchunk(b *testing.B) {
	benchmarkTCPLoopback(4*1024, b, true)
}

func BenchmarkSplice64KBchunk(b *testing.B) {
	benchmarkTCPLoopback(64*1024, b, true)
}

func BenchmarkCopy1KBchunk(b *testing.B) {
	benchmarkTCPLoopback(1024, b, false)
}

func BenchmarkCopy4KBchunk(b *testing.B) {
	benchmarkTCPLoopback(4*1024, b, false)
}

func BenchmarkCopy64KBchunk(b *testing.B) {
	benchmarkTCPLoopback(64*1024, b, false)
}
