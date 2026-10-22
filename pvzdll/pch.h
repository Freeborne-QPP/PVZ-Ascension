// pch.h: ����Ԥ�����ͷ�ļ���
// �·��г����ļ�������һ�Σ�����˽������ɵ��������ܡ�
// �⻹��Ӱ�� IntelliSense ���ܣ�����������ɺ��������������ܡ�
// ���ǣ�����˴��г����ļ��е��κ�һ��������֮���и��£�����ȫ�����������±��롣
// �����ڴ˴�����ҪƵ�����µ��ļ����⽫ʹ������������Ч��

#ifndef PCH_H
#define PCH_H

// ����Ҫ�ڴ˴�Ԥ����ı�ͷ
#include "framework.h"
typedef unsigned char byte;
#include "../pvzclass/pvzclass.h"
#include "../pvzclass/Events/ProjectileImageEvent.hpp"


extern "C"
{
	__declspec(dllexport) void init();
	__declspec(dllexport) void onAppUpdate(DWORD appAddress);
	__declspec(dllexport) void onCoinCollect(DWORD coinAddress);
	__declspec(dllexport) void onCoinCreate(DWORD coinAddress);
	__declspec(dllexport) void onCoinRemove(DWORD coinAddress);
	__declspec(dllexport) int onDialogButtonDepress(int buttonId, int dialogId);
	__declspec(dllexport) void onDialogDraw(DWORD graphics, Sexy::PDialog dialog);
	__declspec(dllexport) void onDrawUITop(DWORD graphics);
	__declspec(dllexport) void onDrawPlantReanim(DWORD plantAddress, DWORD animationAddress);
	__declspec(dllexport) int onDrawZombieReanim(DWORD zombieAddress, DWORD animationAddress);
	__declspec(dllexport) void onNewGame();
	__declspec(dllexport) void onPlantCreate(DWORD plantAddress);
	__declspec(dllexport) int onPlantReload(DWORD plantAddress, int cd);
	__declspec(dllexport) void onPlantRemove(DWORD plantAddress);
	__declspec(dllexport) void onPeaOnFire(DWORD projectileAddress);
	__declspec(dllexport) int onProjectileCollision(DWORD projectileAddress);
	__declspec(dllexport) void onProjectileCreate(DWORD projectileAddress);
	__declspec(dllexport) DWORD onProjectileHitPlant(DWORD projectileAddress, DWORD plantAddress);
	__declspec(dllexport) DWORD onProjectileHitZombie(DWORD projectileAddress, DWORD zombieAddress);
	__declspec(dllexport) int onProjectileRemove(DWORD projectileAddress);
	__declspec(dllexport) void onGameObjectsUpdate(DWORD boardAddress);
	__declspec(dllexport) void onSeedCardClick(DWORD seedcardAddress);
	__declspec(dllexport) void onZombieBlast(DWORD zombieAddress);
	__declspec(dllexport) void onZombieButter(DWORD zombieAddress);
	__declspec(dllexport) void onZombieDecelerate(DWORD zombieAddress);
	__declspec(dllexport) void onZombieEat(DWORD zombieAddress, DWORD plantAddress);
	__declspec(dllexport) void onZombieFroze(DWORD zombieAddress);
	__declspec(dllexport) int onZombieHit(DWORD zombieAddress, DWORD typeCode, DWORD amount);
	__declspec(dllexport) void onZombieHypnotize(DWORD zombieAddress);
	__declspec(dllexport) void onZombieRemove(DWORD zombieAddress);
	__declspec(dllexport) void onZombieInitAfter(DWORD zombieAddress);
	__declspec(dllexport) void onPlantDamageZombie(DWORD infoPtr);
	__declspec(dllexport) int onPlantAddProjectile(DWORD plantAddress, DWORD projectileAddress, DWORD targetZombieAddress);
	__declspec(dllexport) void onBoardInitAfter(DWORD boardAddress);
	__declspec(dllexport) int GetProjectileImage(DWORD projectileAddress, int imgParam);

}

#endif //PCH_H


