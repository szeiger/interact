package de.szeiger.interact.offheap

import scala.collection.mutable

object MemoryDebugger extends ProxyAllocator {
  private[this] var parent: ProxyAllocator = _

  def setParent(p: ProxyAllocator): Unit = {
    objects.clear()
    parent = p
  }

  private[this] final class Obj(val address: Long, val length: Long, val proxied: Boolean) {
    override def toString = s"[$address..${address+length}["
  }

  private[this] val objects = mutable.TreeMap.empty[Long, Obj](implicitly[Ordering[Long]].reverse)

  private[this] def find(o: Long, accessLen: Int): Obj = {
    val it = objects.valuesIteratorFrom(o)
    if(!it.hasNext) throw new AssertionError(s"Address $o is before all allocated objects")
    val v = it.next()
    if(o + accessLen > v.address + v.length)
      throw new AssertionError(s"Address $o with access length $accessLen is outside of object $v")
    v
  }

  def dispose(): Unit = {
    parent.dispose()
    objects.clear()
  }

  def alloc(len: Long): Long = {
    val o = parent.alloc(len)
    objects.put(o, new Obj(o, len, false))
    if(o % 8 != 0) throw new AssertionError(s"alloc($len) returned non-aligned address $o")
    o
  }

  def free(address: Long, len: Long): Unit = {
    val obj = find(address, 0)
    if(obj.address != address) throw new AssertionError(s"free($address, $len) not called with base address of $obj")
    if(obj.proxied) throw new AssertionError(s"free($address, $len) called on proxied object")
    parent.free(address, len)
    objects.remove(address)
  }

  def allocProxied(len: Long): Long = {
    val o = parent.allocProxied(len)
    objects.put(o, new Obj(o, len, true))
    if(o % 8 != 0) throw new AssertionError(s"allocProxied($len) returned non-aligned address $o")
    o
  }

  def freeProxied(address: Long, len: Long): Unit = {
    val obj = find(address, 0)
    if(obj.address != address) throw new AssertionError(s"freeProxied($address, $len) not called with base address of $obj")
    if(!obj.proxied) throw new AssertionError(s"freeProxied($address, $len) called on non-proxied object")
    parent.freeProxied(address, len)
    objects.remove(address)
  }

  def getProxyPage(address: Long): AnyRef = {
    val obj = find(address, 0)
    if(obj.address != address) throw new AssertionError(s"getProxyPage($address) not called with base address of $obj")
    if(!obj.proxied) throw new AssertionError(s"getProxyPage($address) called on non-proxied object")
    parent.getProxyPage(address)
  }

  def getProxy(address: Long): AnyRef = {
    val obj = find(address, 0)
    if(obj.address != address) throw new AssertionError(s"getProxy($address) not called with base address of $obj")
    if(!obj.proxied) throw new AssertionError(s"getProxy($address) called on non-proxied object")
    parent.getProxy(address)
  }

  def setProxy(address: Long, value: AnyRef): Unit = {
    val obj = find(address, 0)
    if(obj.address != address) throw new AssertionError(s"setProxy($address, $obj) not called with base address of $obj")
    if(!obj.proxied) throw new AssertionError(s"setProxy($address, $obj) called on non-proxied object")
    parent.setProxy(address, value)
  }

  def putInt(address: Long, value: Int): Unit = {
    val obj = find(address, 4)
    if(obj.proxied && address == obj.address + 4) throw new AssertionError(s"Overwriting 32-bit payload of proxied object")
    Allocator.putInt(address, value)
  }

  def getInt(address: Long): Int = {
    val obj = find(address, 4)
    Allocator.getInt(address)
  }

  def putLong(address: Long, value: Long): Unit = {
    val obj = find(address, 8)
    if(obj.proxied && address == obj.address) throw new AssertionError(s"Overwriting 32-bit payload of proxied object")
    Allocator.putLong(address, value)
  }

  def getLong(address: Long): Long = {
    val obj = find(address, 8)
    Allocator.getLong(address)
  }
}
